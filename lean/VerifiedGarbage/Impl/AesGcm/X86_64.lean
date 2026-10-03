import VerifiedGarbage.Impl.Aes.X86_64.Callee
import VerifiedGarbage.Impl.Aes.X86_64.ExpandKey
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul

/-!
# AES-GCM: x86-64 implementation

The AES-GCM functions of `Spec/Gcm/Contract.lean`, composed of calls of the
verified `vg_aes_expand_key`, `vg_aes_ctr32` and `vg_ghash`. They are generic
over the implementations of those they call (`Callees`): each is emitted once
for each implementation of `vg_aes_ctr32` (with the `vg_aes_expand_key` for
the same CPUs) and of `vg_ghash`.

## The working space

Every function has a buffer `W` of 2560 bytes (`scratch` or `work`):

* `[0, 16)`: the tag (written by `finish`, `verify` and `seal`; the received
  tag of `verify` and `open`);
* `[16, 96)`: the streaming state of `seal` and `open`;
* `[96, 112)`: a block `T`: a partial block padded with zeros, or the
  lengths block;
* `[112, 128)`: the tag `open` computes;
* `[128, 176)`: our caller's `rbx, rbp, r12–r15`;
* `[176, 240)`: public values kept across calls (`roundsO`, …; `seal` and
  `open` keep the whole length at `tlenO` and what is left of the data after
  its whole blocks at `dataO` and `lenO`);
* `[240, 256)` and `[256, 272)`: the two tags compared, padded with zeros;
* `[512, 2560)`: the working space of the functions called, and
  `[448, 2560)` that of `vg_aes_gcm_encrypt_blocks` and
  `vg_aes_gcm_decrypt_blocks`.

## Registers

`r15` holds `W`, `r14` the streaming state and `r13` the key context
throughout; the functions called preserve them. The pieces below (`absorb`,
`crypt`, …) take their arguments in `r12` (a pointer), `rbp` (a length) and
`rbx` (an offset or a length), which the callees also preserve; the number of
rounds is kept in `W` (`roundsO`) and loaded before each call of
`vg_aes_ctr32`.

## The pieces

* `absorb yo`: GHASH, with the accumulator at `r14 + yo` and the partial
  block at `r14 + 32` holding `rbx` bytes, absorbs the `rbp` bytes at `r12`:
  the partial block filled first (and absorbed if full), then whole blocks,
  then the last bytes buffered.
* `flush yo`: the `rbx` buffered bytes padded with zeros, and absorbed.
* `lens yo`: the lengths block of `rbx` bytes of additional data and `rbp`
  bytes of text, absorbed.
* `crypt`: the `rbp` bytes at `r12` XORed with the keystream, `rbx` bytes into
  the current keystream block: the rest of that block (at `r14 + 64`), then
  whole blocks with `vg_aes_ctr32` from the counter block at `r14 + 48`, then
  a new keystream block for the last bytes.
* `tag o`: the lengths block absorbed, and `GHASH ⊕ CIPH_K(J₀)` written to
  `W + o`, with `vg_aes_ctr32` on it with the counter block `J₀` (at `r14`).
* `j0`: `J₀` for the `rbp`-byte nonce at `r12` (GHASH'd with `absorb`,
  `flush` and `lens` unless it is 12 bytes), and the state's accumulator and
  first counter block `inc₃₂(J₀)` (`initState`).
* `recv`, `cmp o`: the received tag and the computed one (at `W + o`), each
  of `rbx` bytes, padded with zeros; `eax` is 1 if they are equal and 0 if
  not, without a branch.
* `oneBlocks f`: `seal` and `open` encrypt or decrypt the whole blocks of the
  data and absorb them in one call of `f` (`vg_aes_gcm_encrypt_blocks` or
  `vg_aes_gcm_decrypt_blocks`), which can interleave the two; the pieces
  above then handle the last bytes. When the tag is wrong, `oneUndo`
  encrypts the whole blocks `open` decrypted again.

Only the pointers, the lengths, `rounds`, `tag_len` and (for `open`) whether
the tag is right can affect timing: the branches are on those, and the
comparison is masked.
-/

namespace VG.Impl.AesGcm.X86_64

open VG.X86_64

/-- A function to call: its symbol and its code. -/
structure Fn where
  name : String
  code : Prog isa

/-- The implementations called: of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`, and the instances of `vg_aes_gcm_encrypt_blocks` and
`vg_aes_gcm_decrypt_blocks` that call them. -/
structure Callees where
  ctr : Fn
  key : Fn
  gh : Fn
  enc : Fn
  dec : Fn

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-- `r + k` into `d`. -/
def ptr (d r : Reg) (k : Nat) : List Instr := [.mov d (.reg r), .alu .add d (imm k)]

/-! ## The working space -/

def stO : Nat := 16
def tO : Nat := 96
def uO : Nat := 112
def roundsO : Nat := 176
def alenO : Nat := 184
def tlenO : Nat := 192
def dataO : Nat := 200
def lenO : Nat := 208
def auxO : Nat := 216
def tlO : Nat := 224
def aadO : Nat := 232
def vO : Nat := 240
def rO : Nat := 256
def scrO : Nat := 512
def bScrO : Nat := 448

def saved : List (Reg × Nat) :=
  [(.rbx, 128), (.rbp, 136), (.r12, 144), (.r13, 152), (.r14, 160), (.r15, 168)]

/-- Saves our caller's registers at `b + 128`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store (at_ b d) r

/-- Restores them, with `r15` (restored last) holding `W`. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-! ## Loops -/

/-- `[rsi + r10]`, `[rdi + r10]`. -/
def srcB : MemOp := { base := .rsi, index := some .r10 }
def dstB : MemOp := { base := .rdi, index := some .r10 }

/-- Copies the `rcx` (at least 1) bytes at `rsi` to `rdi`. -/
def copyLoop : Prog isa :=
  .seq (.block [.mov32 .r10 (imm 0)])
    (.loop (.block [.movzx8 .rax srcB, .store8 dstB .rax, .alu .add .r10 (imm 1),
      .alu .cmp .r10 (.reg .rcx)]) .ne)

/-- XORs the `rcx` (at least 1) bytes at `rsi` into those at `rdi`. -/
def xorLoop : Prog isa :=
  .seq (.block [.mov32 .r10 (imm 0)])
    (.loop (.block [.movzx8 .rax dstB, .movzx8 .r11 srcB, .alu .xor .rax (.reg .r11), .store8 dstB .rax,
      .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)]) .ne)

/-- `rcx := min (16 - rbx, rbp)`. -/
def minLen : Prog isa :=
  .seq (.block [.mov32 .rcx (imm 16), .alu .sub .rcx (.reg .rbx), .alu .cmp .rbp (.reg .rcx)])
    (.ite .b (.block [.mov .rcx (.reg .rbp)]) (.block []))

/-- The `rbp` bytes at `r12` split into whole blocks and the rest: `p := r12`,
`k :=` the number of whole blocks, and `r12`, `rbp` the rest. -/
def splitWhole (p k : Reg) : List Instr :=
  [.mov p (.reg .r12), .mov k (.reg .rbp), .shift .shr k 4, .mov .rax (.reg .rbp),
    .alu .and .rbp (imm 15), .alu .sub .rax (.reg .rbp), .alu .add .r12 (.reg .rax)]

variable (c : Callees)

/-! ## GHASH -/

/-- `vg_ghash` of the block at `b + o` into the accumulator at `r14 + yo`. -/
def ghash1 (yo : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .rdx b o ++ [.mov32 .rcx (imm 1)] ++
    ptr .r8 .r15 scrO))
    (.call c.gh.name c.gh.code)

/-- The buffer filled from `r12`, and absorbed if full. -/
def absorbHead (yo : Nat) : Prog isa :=
  .seq minLen
  (.seq (.block [.mov .rdi (.reg .r14), .alu .add .rdi (.reg .rbx), .alu .add .rdi (imm 32),
    .mov .rsi (.reg .r12)])
  (.seq copyLoop
  (.seq (.block [.alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx), .alu .add .rbx (.reg .rcx),
    .alu .cmp .rbx (imm 16)])
    (.ite .e (ghash1 c yo .r14 32) (.block [])))))

/-- The whole blocks at `r12` absorbed. -/
def absorbWhole (yo : Nat) : Prog isa :=
  .seq (.block (splitWhole .rdx .rcx ++ [.alu .test .rcx (.reg .rcx)]))
    (.ite .e (.block [])
      (.seq (.block (ptr .rdi .r13 240 ++ ptr .rsi .r14 yo ++ ptr .r8 .r15 scrO))
        (.call c.gh.name c.gh.code)))

/-- The last `rbp` bytes at `r12` buffered. -/
def absorbTail : Prog isa :=
  .seq (.block [.mov .rcx (.reg .rbp), .alu .test .rcx (.reg .rcx)])
    (.ite .e (.block []) (.seq (.block (ptr .rdi .r14 32 ++ [.mov .rsi (.reg .r12)])) copyLoop))

def absorb (yo : Nat) : Prog isa :=
  .seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.seq (.block [.alu .test .rbx (.reg .rbx)])
      (.seq (.ite .e (.block []) (absorbHead c yo))
      (.seq (absorbWhole c yo) absorbTail))))

/-- The `rbx` buffered bytes, padded with zeros in `T`, absorbed. -/
def flush (yo : Nat) : Prog isa :=
  .seq (.block [.alu .test .rbx (.reg .rbx)])
    (.ite .e (.block [])
      (.seq (.block ([.mov32 .rax (imm 0), .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax] ++
          ptr .rdi .r15 tO ++ ptr .rsi .r14 32 ++ [.mov .rcx (.reg .rbx)]))
      (.seq copyLoop (ghash1 c yo .r15 tO))))

/-- `8 r`, big-endian, into `W + o`. -/
def be64Store (r : Reg) (o : Nat) : List Instr :=
  [.mov .rax (.reg r), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .bswap .rax, .store (at_ .r15 o) .rax]

/-- The lengths block of `rbx` and `rbp` bytes, absorbed. -/
def lens (yo : Nat) : Prog isa :=
  .seq (.block (be64Store .rbx tO ++ be64Store .rbp (tO + 8))) (ghash1 c yo .r15 tO)

/-! ## Counter mode -/

/-- The rest of the keystream block, from byte `rbx`, into `r12`. -/
def cryptHead : Prog isa :=
  .seq minLen
  (.seq (.block [.mov .rdi (.reg .r12), .mov .rsi (.reg .r14), .alu .add .rsi (.reg .rbx),
    .alu .add .rsi (imm 64)])
  (.seq xorLoop (.block [.alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx)])))

/-- Whole blocks at `r12`, by `vg_aes_ctr32`. -/
def cryptWhole : Prog isa :=
  .seq (.block (splitWhole .rcx .r8 ++ [.alu .test .r8 (.reg .r8)]))
    (.ite .e (.block [])
      (.seq (.block ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r14 48 ++
          ptr .r9 .r15 scrO))
        (.call c.ctr.name c.ctr.code)))

/-- The last `rbp` bytes at `r12`, with a new keystream block. -/
def cryptTail : Prog isa :=
  .seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.seq (.block ([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
          .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r14 48 ++
          ptr .rcx .r14 64 ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO))
      (.seq (.call c.ctr.name c.ctr.code)
        (.seq (.block ([.mov .rdi (.reg .r12)] ++ ptr .rsi .r14 64 ++ [.mov .rcx (.reg .rbp)])) xorLoop))))

def crypt : Prog isa :=
  .seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.seq (.block [.alu .test .rbx (.reg .rbx)])
      (.seq (.ite .e (.block []) cryptHead)
      (.seq (cryptWhole c) (cryptTail c)))))

/-! ## The tag and `J₀` -/

/-- The tag into `W + o`. -/
def tag (o : Nat) : Prog isa :=
  .seq (lens c 16)
  (.seq (.block ([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax, .mov .rax (.mem (at_ .r14 24)),
      .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)),
      .mov .rdx (.reg .r14)] ++ ptr .rcx .r15 o ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO))
    (.call c.ctr.name c.ctr.code))

/-- `J₀` of a 12-byte nonce: its three words and `0x00000001` (big-endian). -/
def j012 : List Instr :=
  [.mov32 .rax (.mem (at_ .r12 0)), .mov32 .rcx (.mem (at_ .r12 4)), .mov32 .rdx (.mem (at_ .r12 8)),
    .mov32 .rsi (imm 0x01000000), .store32 (at_ .r14 0) .rax, .store32 (at_ .r14 4) .rcx,
    .store32 (at_ .r14 8) .rdx, .store32 (at_ .r14 12) .rsi]

/-- `J₀` of any other nonce. -/
def j0hash : Prog isa :=
  .seq (.block [.mov32 .rax (imm 0), .store (at_ .r14 0) .rax, .store (at_ .r14 8) .rax,
    .store (at_ .r15 auxO) .rbp, .mov32 .rbx (imm 0)])
  (.seq (absorb c 0)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 auxO)), .alu .and .rbx (imm 15)])
  (.seq (flush c 0)
  (.seq (.block [.mov32 .rbx (imm 0), .mov .rbp (.mem (at_ .r15 auxO))])
    (lens c 0)))))

/-- The first counter block `inc₃₂(J₀)`, word by word, and the accumulator zeroed. -/
def initState : List Instr :=
  [.mov32 .rax (.mem (at_ .r14 0)), .mov32 .rcx (.mem (at_ .r14 4)), .mov32 .rdx (.mem (at_ .r14 8)),
    .mov32 .rsi (.mem (at_ .r14 12)), .bswap32 .rsi, .alu32 .add .rsi (imm 1), .bswap32 .rsi,
    .store32 (at_ .r14 48) .rax, .store32 (at_ .r14 52) .rcx, .store32 (at_ .r14 56) .rdx,
    .store32 (at_ .r14 60) .rsi, .mov32 .rax (imm 0), .store (at_ .r14 16) .rax, .store (at_ .r14 24) .rax]

/-- The streaming state for the `rbp`-byte nonce at `r12`. -/
def j0 : Prog isa :=
  .seq (.block [.alu .cmp .rbp (imm 12)])
    (.seq (.ite .e (.block j012) (j0hash c)) (.block initState))

/-! ## Comparing tags -/

/-- The `rbx` bytes of the received tag (at `W`), padded with zeros at `W + rO`. -/
def recv : Prog isa :=
  .seq (.block ([.mov32 .rax (imm 0), .store (at_ .r15 rO) .rax, .store (at_ .r15 (rO + 8)) .rax] ++
    ptr .rdi .r15 rO ++ [.mov .rsi (.reg .r15), .mov .rcx (.reg .rbx)]))
    copyLoop

/-- The first `rbx` bytes of the tag at `W + o`, padded with zeros at
`W + vO`, compared with the received one: `eax = 1` if they are equal. -/
def cmp (o : Nat) : Prog isa :=
  .seq (.block ([.mov32 .rax (imm 0), .store (at_ .r15 vO) .rax, .store (at_ .r15 (vO + 8)) .rax] ++
    ptr .rdi .r15 vO ++ ptr .rsi .r15 o ++ [.mov .rcx (.reg .rbx)]))
  (.seq copyLoop
    (.block [.mov .rax (.mem (at_ .r15 vO)), .alu .xor .rax (.mem (at_ .r15 rO)),
      .mov .rdx (.mem (at_ .r15 (vO + 8))), .alu .xor .rdx (.mem (at_ .r15 (rO + 8))),
      .alu .or .rax (.reg .rdx), .alu .cmp .rax (imm 1), .mov32 .rax (imm 0), .alu32 .adc .rax (imm 0)]))

/-- ZF is clear iff the tag length `rbx` is one §5.2.1.2 allows (4, 8 or 12 to 16). -/
def tagLenOk : Prog isa :=
  .seq (.block [.mov32 .rcx (imm 0), .alu .cmp .rbx (imm 4)])
  (.seq (.ite .e (.block [.mov32 .rcx (imm 1)]) (.block []))
  (.seq (.block [.alu .cmp .rbx (imm 8)])
  (.seq (.ite .e (.block [.mov32 .rcx (imm 1)]) (.block []))
  (.seq (.block [.alu .cmp .rbx (imm 12)])
  (.seq (.ite .b (.block [])
      (.seq (.block [.alu .cmp .rbx (imm 17)]) (.ite .b (.block [.mov32 .rcx (imm 1)]) (.block []))))
    (.block [.alu .test .rcx (.reg .rcx)]))))))

/-! ## The functions -/

/-- `vg_aes_gcm_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def init : Prog isa :=
  .seq (.block (save .rcx ++ [.mov .r15 (.reg .rcx), .mov .r13 (.reg .rdx), .mov .rbx (.reg .rsi),
      .shift .shr .rbx 2, .alu .add .rbx (imm 6)] ++ ptr .rcx .r15 scrO))
  (.seq (.call c.key.name c.key.code)
  (.seq (.block ([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
      .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13),
      .mov .rsi (.reg .rbx)] ++ ptr .rdx .r15 tO ++ ptr .rcx .r13 240 ++ [.mov32 .r8 (imm 1)] ++
      ptr .r9 .r15 scrO))
  (.seq (.call c.ctr.name c.ctr.code)
    (.block restore))))

/-- `vg_aes_gcm_stream_init(ctx = rdi, nonce = rsi, nonce_len = rdx, state = rcx, scratch = r8)`. -/
def streamInit : Prog isa :=
  .seq (.block (save .r8 ++ [.mov .r15 (.reg .r8), .mov .r14 (.reg .rcx), .mov .r13 (.reg .rdi),
      .mov .r12 (.reg .rsi), .mov .rbp (.reg .rdx)]))
  (.seq (j0 c) (.block restore))

/-- `vg_aes_gcm_stream_aad(ctx = rdi, state = rsi, aad_len = rdx, data = rcx, len = r8, scratch = r9)`. -/
def streamAad : Prog isa :=
  .seq (.block (save .r9 ++ [.mov .r15 (.reg .r9), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi),
      .mov .r12 (.reg .rcx), .mov .rbp (.reg .r8), .mov .rbx (.reg .rdx), .alu .and .rbx (imm 15)]))
  (.seq (absorb c 16) (.block restore))

/-- The entry of `encrypt` and `decrypt`: `(ctx = rdi, rounds = rsi, state = rdx,
aad_len = rcx, text_len = r8, data = r9, len = [rsp + 8], scratch = [rsp + 16])`. -/
def cryptEntry : List Instr :=
  [.mov .rax (.mem (at_ .rsp 16))] ++ save .rax ++
    [.mov .r15 (.reg .rax), .mov .r14 (.reg .rdx), .mov .r13 (.reg .rdi),
      .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 alenO) .rcx, .store (at_ .r15 tlenO) .r8,
      .store (at_ .r15 dataO) .r9, .mov .rbp (.mem (at_ .rsp 8)), .store (at_ .r15 lenO) .rbp,
      .mov .r12 (.reg .r9), .mov .rbx (.reg .r8), .alu .and .rbx (imm 15)]

/-- The additional data padded, before the first text. -/
def firstFlush : Prog isa :=
  .seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .alu .and .rbx (imm 15)]) (flush c 16)

/-- The text (`len` bytes at `data`, as kept) absorbed into GHASH. -/
def textAbsorb : Prog isa :=
  .seq (.block [.mov .rbp (.mem (at_ .r15 lenO)), .alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (firstFlush c) (.block []))
      (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)),
          .mov .rbx (.mem (at_ .r15 tlenO)), .alu .and .rbx (imm 15)])
        (absorb c 16)))))

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa :=
  .seq (.block cryptEntry) (.seq (crypt c) (.seq (textAbsorb c) (.block restore)))

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa :=
  .seq (.block cryptEntry)
  (.seq (textAbsorb c)
  (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)),
      .mov .rbx (.mem (at_ .r15 tlenO)), .alu .and .rbx (imm 15)])
  (.seq (crypt c) (.block restore))))

/-- The entry of `finish` and `verify`: `(ctx = rdi, rounds = rsi, state = rdx,
aad_len = rcx, text_len = r8, work = r9)`. -/
def finEntry : List Instr :=
  save .r9 ++ [.mov .r15 (.reg .r9), .mov .r14 (.reg .rdx), .mov .r13 (.reg .rdi),
    .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 alenO) .rcx, .store (at_ .r15 tlenO) .r8]

/-- The buffered bytes padded and absorbed, and the tag into `W + o`. -/
def finTag (o : Nat) : Prog isa :=
  .seq (.block [.mov .rbx (.mem (at_ .r15 tlenO)), .mov .rax (.mem (at_ .r15 alenO)),
      .alu .test .rbx (.reg .rbx)])
  (.seq (.ite .e (.block [.mov .rbx (.reg .rax)]) (.block []))
  (.seq (.block [.alu .and .rbx (imm 15)])
  (.seq (flush c 16)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .mov .rbp (.mem (at_ .r15 tlenO))])
    (tag c o)))))

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinish : Prog isa :=
  .seq (.block finEntry) (.seq (finTag c 0) (.block restore))

/-- `vg_aes_gcm_stream_verify`, with `tag_len = [rsp + 8]`. -/
def streamVerify : Prog isa :=
  .seq (.block (finEntry ++ [.mov .rbx (.mem (at_ .rsp 8)), .store (at_ .r15 tlO) .rbx]))
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov32 .rax (imm 0), .store (at_ .r15 0) .rax, .store (at_ .r15 8) .rax])
      (.seq recv
      (.seq (finTag c 0)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))])
      (.seq (cmp 0)
        (.block [.mov32 .rcx (imm 0), .alu .sub .rcx (.reg .rax), .mov .rdx (.mem (at_ .r15 0)),
          .alu .and .rdx (.reg .rcx), .store (at_ .r15 0) .rdx, .mov .rdx (.mem (at_ .r15 8)),
          .alu .and .rdx (.reg .rcx), .store (at_ .r15 8) .rdx]))))))
    (.block restore)))

/-- The entry of `seal` and `open`: `(ctx = rdi, rounds = rsi, nonce = rdx,
nonce_len = rcx, aad = r8, aad_len = r9, data = [rsp + 8], len = [rsp + 16],
work = [rsp + 24])`. The state is at `W + 16`. -/
def oneEntry : List Instr :=
  [.mov .rax (.mem (at_ .rsp 24))] ++ save .rax ++
    [.mov .r15 (.reg .rax)] ++ ptr .r14 .r15 stO ++
    [.mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 aadO) .r8,
      .store (at_ .r15 alenO) .r9, .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 dataO) .rax,
      .mov .rax (.mem (at_ .rsp 16)), .store (at_ .r15 lenO) .rax, .mov .r12 (.reg .rdx),
      .mov .rbp (.reg .rcx)]

/-- `J₀`, then the additional data absorbed and padded. -/
def oneAad : Prog isa :=
  .seq (j0 c)
  (.seq (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)])
  (.seq (absorb c 16)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .alu .and .rbx (imm 15)])
    (flush c 16))))

/-- The whole blocks of the data encrypted (with `f`, `vg_aes_gcm_encrypt_blocks`)
or decrypted (`vg_aes_gcm_decrypt_blocks`) and absorbed, from the first counter
block, in one call: the counter at `r14 + 48`, the accumulator at `r14 + 16`
and `scratch` at `W + 448`, passed on the stack. The data kept then becomes
what is left, the last `len mod 16` bytes, and `len` itself stays at
`W + 192`. -/
def oneBlocks (f : Fn) : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .store (at_ .r15 tlenO) .rax, .shift .shr .rax 4,
      .alu .test .rax (.reg .rax)])
    (.ite .e (.block [])
      (.seq (.block ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r14 48 ++
          ptr .rcx .r14 16 ++ [.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] ++ ptr .rax .r15 bScrO))
        (.seq (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1))
          (.block [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15),
            .store (at_ .r15 lenO) .rcx, .alu .sub .rax (.reg .rcx), .alu .add .rax (.mem (at_ .r15 dataO)),
            .store (at_ .r15 dataO) .rax]))))

/-- The data left (as ciphertext) absorbed and padded, and the tag of all of it
(`len` at `W + 192`) into `W + o`. -/
def oneTag (o : Nat) : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)])
  (.seq (absorb c 16)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 lenO)), .alu .and .rbx (imm 15)])
  (.seq (flush c 16)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .mov .rbp (.mem (at_ .r15 tlenO))])
    (tag c o)))))

/-- The data encrypted or decrypted, from the first counter block. -/
def oneCrypt : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)])
    (crypt c)

/-- The whole blocks decrypted by `oneBlocks`, encrypted again (when the tag
is wrong): `vg_aes_ctr32` from the first counter block, at the data's start
(`len - len mod 16` bytes before the data kept). -/
def oneUndo : Prog isa :=
  .seq (.block ([.mov .rax (.mem (at_ .r15 tlenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15),
      .alu .sub .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 dataO)), .alu .sub .rcx (.reg .rax),
      .shift .shr .rax 4, .mov .r8 (.reg .rax), .alu .test .rax (.reg .rax)]))
    (.ite .e (.block [])
      (.seq (.block (initState ++ [.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++
          ptr .rdx .r14 48 ++ ptr .r9 .r15 scrO))
        (.call c.ctr.name c.ctr.code)))

/-- `vg_aes_gcm_seal`. -/
def «seal» : Prog isa :=
  .seq (.block oneEntry) (.seq (oneAad c) (.seq (oneBlocks c.enc) (.seq (oneCrypt c) (.seq (oneTag c 0)
    (.block restore)))))

/-- `vg_aes_gcm_open`, with `tag_len = [rsp + 32]`. -/
def «open» : Prog isa :=
  .seq (.block (oneEntry ++ [.mov .rbx (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rbx]))
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov32 .rax (imm 0)])
      (.seq (oneAad c)
      (.seq (oneBlocks c.dec)
      (.seq (oneTag c uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))])
      (.seq recv
      (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (oneUndo c) (oneCrypt c))
        (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))))
    (.block restore)))

end VG.Impl.AesGcm.X86_64

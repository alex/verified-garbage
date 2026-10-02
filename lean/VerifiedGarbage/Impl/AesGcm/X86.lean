import VerifiedGarbage.Impl.Aes.X86.Ctr32
import VerifiedGarbage.Impl.Aes.X86.ExpandKey
import VerifiedGarbage.Impl.Gcm.X86

/-!
# AES-GCM: x86 (32-bit) implementation

The AES-GCM functions of `Spec/Gcm/Contract.lean`, cdecl (every argument on
the stack), composed of calls of the verified `vg_aes_expand_key`,
`vg_aes_ctr32` and `vg_ghash`, as on x86-64 (`Impl/AesGcm/X86_64.lean`),
whose algorithm and pieces these follow.

## The working space

Every function has a buffer `W` of 2560 bytes (`scratch` or `work`):

* `[0, 16)`: the tag (written by `finish`, `verify` and `seal`; the received
  tag of `verify` and `open`);
* `[16, 96)`: the streaming state of `seal` and `open`;
* `[96, 112)`: a block `T`: a partial block padded with zeros, or the
  lengths block;
* `[112, 128)`: the tag `open` computes;
* `[128, 144)`: our caller's `ebx`, `esi`, `edi`, `ebp`;
* `[144, 240)`: the values kept for the whole function (`ctxO`, …), copied
  from the arguments on entry;
* `[240, 256)` and `[256, 272)`: the two tags compared, padded with zeros;
* `[272, 288)`: the arguments of the piece running (`dO`, `nO`, `bO`);
* `[512, 2560)`: the working space of the functions called.

## Registers

`ebp` holds `W` and `esi` the streaming state throughout; the functions
called preserve them. Everything else is reloaded from `W`: a piece takes
its arguments from `W + 272` on (`dO`: a pointer, `nO`: a length, `bO`: an
offset). Each call pushes its arguments (last to first) in a frame of its
own, popped into `eax`: `vg_aes_ctr32` six, `vg_ghash` five and
`vg_aes_expand_key` four, with the return address 28 bytes of stack at
most. The working space of the callee, `W + 512`, is passed in `ebp`, which
is moved there before the frame and back after it.

## The pieces

* `absorb yo`: GHASH, with the accumulator at `esi + yo` and the partial
  block at `esi + 32` holding `bO` bytes, absorbs the `nO` bytes at `dO`:
  the partial block filled first (and absorbed if full), then whole blocks,
  then the last bytes buffered.
* `flush yo`: the `bO` buffered bytes padded with zeros, and absorbed.
* `lens yo a a' t t'`: the lengths block of the 64-bit lengths whose words
  are kept at `W + a`, `W + a'` (low, high) and `W + t`, `W + t'`, absorbed.
* `crypt`: the `nO` bytes at `dO` XORed with the keystream, `bO` bytes into
  the current keystream block: the rest of that block (at `esi + 64`), then
  whole blocks with `vg_aes_ctr32` from the counter block at `esi + 48`,
  then a new keystream block for the last bytes.
* `tag o …`: the lengths block absorbed, and `GHASH ⊕ CIPH_K(J₀)` written to
  `W + o`, with `vg_aes_ctr32` on it with the counter block `J₀` (at `esi`).
* `j0`: `J₀` for the `nO`-byte nonce at `dO` (GHASH'd with `absorb`,
  `flush` and `lens` unless it is 12 bytes), and the state's accumulator and
  first counter block `inc₃₂(J₀)` (`initState`).
* `recv`, `cmp o`: the received tag and the computed one (at `W + o`), each
  of `tag_len` bytes, padded with zeros; `eax` is 1 if they are equal and 0
  if not, without a branch.

Only the pointers, the lengths, `rounds`, `tag_len` and (for `open`) whether
the tag is right can affect timing: the branches are on those, and the
comparison is masked.
-/

namespace VG.Impl.AesGcm.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-- `W + o`. -/
def slot (o : Nat) : Src := .mem (at_ .ebp o)

/-- The stack argument `i` (from 0) on entry, `[esp + 4 + 4 i]`. -/
def argOp (i : Nat) : Src := .mem (at_ .esp (4 + 4 * i))

/-! ## The working space -/

abbrev stO : Nat := 16
abbrev tO : Nat := 96
abbrev uO : Nat := 112
abbrev ctxO : Nat := 144
abbrev roundsO : Nat := 148
abbrev alO : Nat := 152
abbrev ahO : Nat := 156
abbrev xlO : Nat := 160
abbrev xhO : Nat := 164
abbrev dataO : Nat := 168
abbrev lenO : Nat := 172
abbrev aadO : Nat := 176
abbrev tglO : Nat := 180
abbrev auxO : Nat := 184
abbrev zO : Nat := 188
abbrev nlO : Nat := 192
abbrev vO : Nat := 240
abbrev rO : Nat := 256
abbrev dO : Nat := 272
abbrev nO : Nat := 276
abbrev bO : Nat := 280
abbrev scrO : Nat := 512

/-- Our caller's registers, saved at `W + 128` (with `W` in `eax`), and `ebp := W`. -/
def saveAt : List Instr :=
  [.store (at_ .eax 128) .ebx, .store (at_ .eax 132) .esi, .store (at_ .eax 136) .edi,
    .store (at_ .eax 140) .ebp, .mov .ebp (.reg .eax)]

/-- Restores them, `ebp` last. -/
def restore : List Instr :=
  [.mov .ebx (slot 128), .mov .esi (slot 132), .mov .edi (slot 136), .mov .ebp (slot 140)]

/-- The stack argument `i` kept at `W + o`. -/
def keep (i o : Nat) : List Instr := [.mov .eax (argOp i), .store (at_ .ebp o) .eax]

/-- The block at `W + o` zeroed (and `eax := 0`). -/
def zero4 (o : Nat) : List Instr :=
  [.mov .eax (imm 0), .store (at_ .ebp o) .eax, .store (at_ .ebp (o + 4)) .eax,
    .store (at_ .ebp (o + 8)) .eax, .store (at_ .ebp (o + 12)) .eax]

/-! ## Calls -/

/-- `vg_aes_ctr32(eax, ecx, edx, ebx, edi, ebp)`. -/
def ctrCall : Prog isa :=
  .frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call "vg_aes_ctr32" Impl.Aes.X86.ctr32) (.pop .eax 6)

/-- `vg_ghash(eax, edx, ebx, edi, ebp)`. -/
def ghCall : Prog isa :=
  .frame (.push [.ebp, .edi, .ebx, .edx, .eax]) (.call "vg_ghash" Impl.Gcm.X86.ghash) (.pop .eax 5)

/-- `vg_aes_expand_key(eax, ecx, edx, ebp)`. -/
def keyCall : Prog isa :=
  .frame (.push [.ebp, .edx, .ecx, .eax]) (.call "vg_aes_expand_key" Impl.Aes.X86.expandKey) (.pop .eax 4)

/-- `ebp` back to `W` after a call. -/
def unscr : List Instr := [.alu .sub .ebp (imm scrO)]

/-! ## Loops -/

/-- Copies the `ecx` (at least 1) bytes at `edi` to `edx`, advancing both. -/
def copyLoop : Prog isa :=
  .loop (.block [.movzx8 .eax (at_ .edi 0), .store8 (at_ .edx 0) .al, .alu .add .edi (imm 1),
    .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]) .ne

/-- XORs the `ecx` (at least 1) bytes at `edx` into those at `edi`, advancing both. -/
def xorLoop : Prog isa :=
  .loop (.block [.movzx8 .eax (at_ .edx 0), .movzx8 .ebx (at_ .edi 0), .alu .xor .eax (.reg .ebx),
    .store8 (at_ .edi 0) .al, .alu .add .edi (imm 1), .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]) .ne

/-- `ecx := min (16 - bO, nO)`. -/
def minLen : Prog isa :=
  .seq (.block [.mov .ecx (imm 16), .alu .sub .ecx (slot bO), .mov .eax (slot nO), .alu .cmp .eax (.reg .ecx)])
    (.ite .b (.block [.mov .ecx (.reg .eax)]) (.block []))

/-- The `nO` bytes at `dO` split into whole blocks and the rest: `ebx := dO`,
`edi :=` the number of whole blocks, and `dO`, `nO` the rest; ZF is set if
there are no whole blocks. -/
def splitWhole : List Instr :=
  [.mov .ebx (slot dO), .mov .edi (slot nO), .shift .shr .edi 4, .mov .eax (slot nO), .mov .edx (.reg .eax),
    .alu .and .edx (imm 15), .store (at_ .ebp nO) .edx, .alu .sub .eax (.reg .edx), .alu .add .eax (.reg .ebx),
    .store (at_ .ebp dO) .eax, .alu .test .edi (.reg .edi)]

/-! ## GHASH -/

/-- The arguments of `vg_ghash` but the data and their number (`ebx`, `edi`):
the hash subkey, the accumulator at `esi + yo` and the working space. -/
def ghArgs (yo : Nat) : List Instr :=
  [.mov .eax (slot ctxO), .alu .add .eax (imm 240), .mov .edx (.reg .esi), .alu .add .edx (imm yo),
    .alu .add .ebp (imm scrO)]

/-- `vg_ghash` of the block at `b + o` into the accumulator at `esi + yo`. -/
def ghash1 (yo : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block ([.mov .ebx (.reg b), .alu .add .ebx (imm o), .mov .edi (imm 1)] ++ ghArgs yo))
    (.seq ghCall (.block unscr))

/-- The buffer filled from `dO`, and absorbed if full. -/
def absorbHead (yo : Nat) : Prog isa :=
  .seq minLen
  (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .esi), .alu .add .edx (imm 32), .alu .add .edx (slot bO),
      .mov .eax (slot nO), .alu .sub .eax (.reg .ecx), .store (at_ .ebp nO) .eax,
      .mov .eax (slot bO), .alu .add .eax (.reg .ecx), .store (at_ .ebp bO) .eax,
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store (at_ .ebp dO) .eax])
  (.seq copyLoop
  (.seq (.block [.mov .eax (slot bO), .alu .cmp .eax (imm 16)])
    (.ite .e (ghash1 yo .esi 32) (.block [])))))

/-- The whole blocks at `dO` absorbed. -/
def absorbWhole (yo : Nat) : Prog isa :=
  .seq (.block splitWhole)
    (.ite .e (.block []) (.seq (.block (ghArgs yo)) (.seq ghCall (.block unscr))))

/-- The last `nO` bytes at `dO` buffered. -/
def absorbTail : Prog isa :=
  .seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block []) (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .esi), .alu .add .edx (imm 32)])
      copyLoop))

def absorb (yo : Nat) : Prog isa :=
  .seq (.block [.mov .eax (slot nO), .alu .test .eax (.reg .eax)])
    (.ite .e (.block [])
      (.seq (.block [.mov .eax (slot bO), .alu .test .eax (.reg .eax)])
      (.seq (.ite .e (.block []) (absorbHead yo))
      (.seq (absorbWhole yo) absorbTail))))

/-- The `bO` buffered bytes, padded with zeros in `T`, absorbed. -/
def flush (yo : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (slot bO), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block [])
      (.seq (.block (zero4 tO ++ [.mov .edi (.reg .esi), .alu .add .edi (imm 32), .mov .edx (.reg .ebp),
          .alu .add .edx (imm tO)]))
      (.seq copyLoop (ghash1 yo .ebp tO))))

/-- `8 x` (modulo 2⁶⁴) for the 64-bit `x` whose words are at `W + lo` and
`W + hi`, big-endian, into `W + o`: each word doubled three times, and the
top 3 bits of the low word added to the high. -/
def be64w (lo hi o : Nat) : List Instr :=
  [.mov .eax (slot lo), .mov .ecx (slot hi), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .alu .add .ecx (.reg .ecx), .mov .edx (.reg .eax), .shift .shr .edx 29, .alu .add .ecx (.reg .edx),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .bswap .ecx,
    .bswap .eax, .store (at_ .ebp o) .ecx, .store (at_ .ebp (o + 4)) .eax]

/-- The lengths block, absorbed. -/
def lens (yo al ah tl th : Nat) : Prog isa :=
  .seq (.block (be64w al ah tO ++ be64w tl th (tO + 8))) (ghash1 yo .ebp tO)

/-! ## Counter mode -/

/-- The arguments of `vg_aes_ctr32` but the data and their number (`ebx`,
`edi`): the key schedule, the rounds, the counter block at `esi + 48` and the
working space. -/
def ctrArgs : List Instr :=
  [.mov .eax (slot ctxO), .mov .ecx (slot roundsO), .mov .edx (.reg .esi), .alu .add .edx (imm 48),
    .alu .add .ebp (imm scrO)]

/-- The rest of the keystream block, from byte `bO`, into `dO`. -/
def cryptHead : Prog isa :=
  .seq minLen
  (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .esi), .alu .add .edx (imm 64), .alu .add .edx (slot bO),
      .mov .eax (slot nO), .alu .sub .eax (.reg .ecx), .store (at_ .ebp nO) .eax,
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store (at_ .ebp dO) .eax])
    xorLoop)

/-- Whole blocks at `dO`, by `vg_aes_ctr32`. -/
def cryptWhole : Prog isa :=
  .seq (.block splitWhole)
    (.ite .e (.block []) (.seq (.block ctrArgs) (.seq ctrCall (.block unscr))))

/-- The last `nO` bytes at `dO`, with a new keystream block. -/
def cryptTail : Prog isa :=
  .seq (.block [.mov .eax (slot nO), .alu .test .eax (.reg .eax)])
    (.ite .e (.block [])
      (.seq (.block ([.mov .eax (imm 0), .store (at_ .esi 64) .eax, .store (at_ .esi 68) .eax,
          .store (at_ .esi 72) .eax, .store (at_ .esi 76) .eax, .mov .ebx (.reg .esi), .alu .add .ebx (imm 64),
          .mov .edi (imm 1)] ++ ctrArgs))
      (.seq (.seq ctrCall (.block unscr))
      (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .esi), .alu .add .edx (imm 64), .mov .ecx (slot nO)])
        xorLoop))))

def crypt : Prog isa :=
  .seq (.block [.mov .eax (slot nO), .alu .test .eax (.reg .eax)])
    (.ite .e (.block [])
      (.seq (.block [.mov .eax (slot bO), .alu .test .eax (.reg .eax)])
      (.seq (.ite .e (.block []) cryptHead)
      (.seq cryptWhole cryptTail))))

/-! ## The tag and `J₀` -/

/-- The tag into `W + o`, for the lengths kept at `W + al`, … -/
def tag (o al ah tl th : Nat) : Prog isa :=
  .seq (lens 16 al ah tl th)
  (.seq (.block [.mov .eax (.mem (at_ .esi 16)), .mov .ecx (.mem (at_ .esi 20)), .mov .edx (.mem (at_ .esi 24)),
      .mov .ebx (.mem (at_ .esi 28)), .store (at_ .ebp o) .eax, .store (at_ .ebp (o + 4)) .ecx,
      .store (at_ .ebp (o + 8)) .edx, .store (at_ .ebp (o + 12)) .ebx, .mov .ebx (.reg .ebp),
      .alu .add .ebx (imm o), .mov .edi (imm 1), .mov .eax (slot ctxO), .mov .ecx (slot roundsO),
      .mov .edx (.reg .esi), .alu .add .ebp (imm scrO)])
    (.seq ctrCall (.block unscr)))

/-- `J₀` of a 12-byte nonce: its words and `0x00000001` (big-endian). -/
def j012 : Prog isa :=
  .seq (.block [.mov .edi (slot dO)])
    (.block [.mov .eax (.mem (at_ .edi 0)), .mov .ecx (.mem (at_ .edi 4)), .mov .edx (.mem (at_ .edi 8)),
      .store (at_ .esi 0) .eax, .store (at_ .esi 4) .ecx, .store (at_ .esi 8) .edx,
      .mov .eax (imm 0x01000000), .store (at_ .esi 12) .eax])

/-- `J₀` of any other nonce. -/
def j0hash : Prog isa :=
  .seq (.block [.mov .eax (imm 0), .store (at_ .esi 0) .eax, .store (at_ .esi 4) .eax, .store (at_ .esi 8) .eax,
      .store (at_ .esi 12) .eax, .store (at_ .ebp bO) .eax])
  (.seq (absorb 0)
  (.seq (.block [.mov .eax (slot nlO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
  (.seq (flush 0) (lens 0 zO zO nlO zO))))

/-- The first counter block `inc₃₂(J₀)`, word by word, and the accumulator zeroed. -/
def initState : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .store (at_ .esi 48) .eax, .mov .eax (.mem (at_ .esi 4)),
    .store (at_ .esi 52) .eax, .mov .eax (.mem (at_ .esi 8)), .store (at_ .esi 56) .eax,
    .mov .eax (.mem (at_ .esi 12)), .bswap .eax, .alu .add .eax (imm 1), .bswap .eax,
    .store (at_ .esi 60) .eax, .mov .eax (imm 0), .store (at_ .esi 16) .eax, .store (at_ .esi 20) .eax,
    .store (at_ .esi 24) .eax, .store (at_ .esi 28) .eax]

/-- The streaming state for the nonce at `dO`, of `nO` bytes (also kept at `W + nlO`). -/
def j0 : Prog isa :=
  .seq (.block [.mov .eax (slot nlO), .alu .cmp .eax (imm 12)])
    (.seq (.ite .e j012 j0hash) (.block initState))

/-! ## Comparing tags -/

/-- The `tag_len` bytes of the received tag (at `W`), padded with zeros at `W + rO`. -/
def recv : Prog isa :=
  .seq (.block (zero4 rO ++ [.mov .edi (.reg .ebp), .mov .edx (.reg .ebp), .alu .add .edx (imm rO),
    .mov .ecx (slot tglO)]))
    copyLoop

/-- The words of `W + vO` and `W + rO` compared: `eax = 1` if they are equal. -/
def cmpTail : List Instr :=
  [.mov .eax (slot vO), .alu .xor .eax (slot rO), .mov .ecx (slot (vO + 4)), .alu .xor .ecx (slot (rO + 4)),
    .alu .or .eax (.reg .ecx), .mov .ecx (slot (vO + 8)), .alu .xor .ecx (slot (rO + 8)),
    .alu .or .eax (.reg .ecx), .mov .ecx (slot (vO + 12)), .alu .xor .ecx (slot (rO + 12)),
    .alu .or .eax (.reg .ecx), .alu .cmp .eax (imm 1), .mov .eax (imm 0), .alu .adc .eax (imm 0)]

/-- The first `tag_len` bytes of the tag at `W + o`, padded with zeros at
`W + vO`, compared with the received one: `eax = 1` if they are equal. -/
def cmp (o : Nat) : Prog isa :=
  .seq (.block (zero4 vO ++ [.mov .edi (.reg .ebp), .alu .add .edi (imm o), .mov .edx (.reg .ebp),
    .alu .add .edx (imm vO), .mov .ecx (slot tglO)]))
  (.seq copyLoop (.block cmpTail))

/-- ZF is clear iff the tag length (at `W + tglO`) is one §5.2.1.2 allows (4, 8 or 12 to 16). -/
def tagLenOk : Prog isa :=
  .seq (.block [.mov .ecx (imm 0), .mov .ebx (slot tglO), .alu .cmp .ebx (imm 4)])
  (.seq (.ite .e (.block [.mov .ecx (imm 1)]) (.block []))
  (.seq (.block [.alu .cmp .ebx (imm 8)])
  (.seq (.ite .e (.block [.mov .ecx (imm 1)]) (.block []))
  (.seq (.block [.alu .cmp .ebx (imm 12)])
  (.seq (.ite .b (.block [])
      (.seq (.block [.alu .cmp .ebx (imm 17)]) (.ite .b (.block [.mov .ecx (imm 1)]) (.block []))))
    (.block [.alu .test .ecx (.reg .ecx)]))))))

/-! ## The functions -/

/-- The entry: `W` (the stack argument `w`) into `eax`, then our caller's
registers saved, `ebp := W`, and `rest`. -/
def entry (w : Nat) (rest : List Instr) : Prog isa :=
  .seq (.block [.mov .eax (argOp w)]) (.block (saveAt ++ rest))

/-- `vg_aes_gcm_init(key, key_len, ctx, scratch)`. -/
def init : Prog isa :=
  .seq (entry 3 [.mov .esi (argOp 2), .mov .ecx (argOp 1), .mov .ebx (.reg .ecx), .shift .shr .ebx 2,
      .alu .add .ebx (imm 6), .mov .eax (argOp 0), .mov .edx (.reg .esi), .alu .add .ebp (imm scrO)])
  (.seq keyCall
  (.seq (.block (unscr ++ [.mov .eax (imm 0), .store (at_ .esi 240) .eax, .store (at_ .esi 244) .eax,
      .store (at_ .esi 248) .eax, .store (at_ .esi 252) .eax] ++ zero4 tO ++
      [.mov .eax (.reg .esi), .mov .ecx (.reg .ebx), .mov .edx (.reg .ebp), .alu .add .edx (imm tO),
        .mov .ebx (.reg .esi), .alu .add .ebx (imm 240), .mov .edi (imm 1), .alu .add .ebp (imm scrO)]))
  (.seq ctrCall
    (.block (unscr ++ restore)))))

/-- `vg_aes_gcm_stream_init(ctx, nonce, nonce_len, state, scratch)`. -/
def streamInit : Prog isa :=
  .seq (entry 4 ([.mov .esi (argOp 3)] ++ keep 0 ctxO ++ keep 1 dO ++ keep 2 nO ++ keep 2 nlO ++
      [.mov .eax (imm 0), .store (at_ .ebp zO) .eax]))
  (.seq j0 (.block restore))

/-- `vg_aes_gcm_stream_aad(ctx, state, aad_len (2 words), data, len, scratch)`. -/
def streamAad : Prog isa :=
  .seq (entry 6 ([.mov .esi (argOp 1)] ++ keep 0 ctxO ++ keep 4 dO ++ keep 5 nO ++
      [.mov .eax (argOp 2), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax]))
  (.seq (absorb 16) (.block restore))

/-- The entry of `encrypt` and `decrypt`: `(ctx, rounds, state, aad_len (2 words),
text_len (2 words), data, len, scratch)`. -/
def cryptEntry : Prog isa :=
  entry 9 ([.mov .esi (argOp 2)] ++ keep 0 ctxO ++ keep 1 roundsO ++ keep 3 alO ++ keep 4 ahO ++
    keep 5 xlO ++ keep 6 xhO ++ keep 7 dataO ++ keep 8 lenO)

/-- The text: `len` bytes at `data`, `text_len mod 16` into the keystream block. -/
def setText : List Instr :=
  [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO), .store (at_ .ebp nO) .eax,
    .mov .eax (slot xlO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax]

/-- The additional data padded, before the first text. -/
def firstFlush : Prog isa :=
  .seq (.block [.mov .eax (slot alO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax]) (flush 16)

/-- The text absorbed into GHASH. -/
def textAbsorb : Prog isa :=
  .seq (.block [.mov .eax (slot lenO), .alu .test .eax (.reg .eax)])
    (.ite .e (.block [])
      (.seq (.block [.mov .eax (slot xlO), .alu .or .eax (slot xhO)])
      (.seq (.ite .e firstFlush (.block []))
      (.seq (.block setText) (absorb 16)))))

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa :=
  .seq cryptEntry (.seq (.block setText) (.seq crypt (.seq textAbsorb (.block restore))))

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa :=
  .seq cryptEntry (.seq textAbsorb (.seq (.block setText) (.seq crypt (.block restore))))

/-- The entry of `finish` and `verify`: `(ctx, rounds, state, aad_len (2 words),
text_len (2 words), work)`, and `rest`. -/
def finEntry (rest : List Instr) : Prog isa :=
  entry 7 ([.mov .esi (argOp 2)] ++ keep 0 ctxO ++ keep 1 roundsO ++ keep 3 alO ++ keep 4 ahO ++
    keep 5 xlO ++ keep 6 xhO ++ rest)

/-- The buffered bytes padded and absorbed, and the tag into `W + o`. -/
def finTag (o : Nat) : Prog isa :=
  .seq (.block [.mov .eax (slot xlO), .mov .ecx (slot alO), .mov .edx (slot xlO), .alu .or .edx (slot xhO)])
  (.seq (.ite .e (.block [.mov .eax (.reg .ecx)]) (.block []))
  (.seq (.block [.alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
  (.seq (flush 16) (tag o alO ahO xlO xhO))))

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinish : Prog isa :=
  .seq (finEntry []) (.seq (finTag 0) (.block restore))

/-- The computed tag at `W` kept if `eax` is 1, zeroed if it is 0. -/
def mask : List Instr :=
  [.mov .ecx (imm 0), .alu .sub .ecx (.reg .eax), .mov .edx (slot 0), .alu .and .edx (.reg .ecx),
    .store (at_ .ebp 0) .edx, .mov .edx (slot 4), .alu .and .edx (.reg .ecx), .store (at_ .ebp 4) .edx,
    .mov .edx (slot 8), .alu .and .edx (.reg .ecx), .store (at_ .ebp 8) .edx, .mov .edx (slot 12),
    .alu .and .edx (.reg .ecx), .store (at_ .ebp 12) .edx]

/-- `vg_aes_gcm_stream_verify`, with `tag_len` the stack argument 8. -/
def streamVerify : Prog isa :=
  .seq (finEntry (keep 8 tglO))
  (.seq tagLenOk
  (.seq (.ite .e (.block (zero4 0))
      (.seq recv (.seq (finTag 0) (.seq (cmp 0) (.block mask)))))
    (.block restore)))

/-- The entry of `seal` and `open`: `(ctx, rounds, nonce, nonce_len, aad,
aad_len, data, len, work)`, and `rest`. The state is at `W + 16`. -/
def oneEntry (rest : List Instr) : Prog isa :=
  entry 8 ([.mov .esi (.reg .ebp), .alu .add .esi (imm stO)] ++ keep 0 ctxO ++ keep 1 roundsO ++ keep 2 dO ++
    keep 3 nO ++ keep 3 nlO ++ keep 4 aadO ++ keep 5 alO ++ keep 6 dataO ++ keep 7 lenO ++
    [.mov .eax (imm 0), .store (at_ .ebp zO) .eax] ++ rest)

/-- `J₀`, then the additional data absorbed and padded. -/
def oneAad : Prog isa :=
  .seq j0
  (.seq (.block [.mov .eax (slot aadO), .store (at_ .ebp dO) .eax, .mov .eax (slot alO),
      .store (at_ .ebp nO) .eax, .mov .eax (imm 0), .store (at_ .ebp bO) .eax])
  (.seq (absorb 16)
  (.seq (.block [.mov .eax (slot alO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
    (flush 16))))

/-- The data, from the start. -/
def setData : List Instr :=
  [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO), .store (at_ .ebp nO) .eax,
    .mov .eax (imm 0), .store (at_ .ebp bO) .eax]

/-- The data (as ciphertext) absorbed and padded, and the tag into `W + o`. -/
def oneTag (o : Nat) : Prog isa :=
  .seq (.block setData)
  (.seq (absorb 16)
  (.seq (.block [.mov .eax (slot lenO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
  (.seq (flush 16) (tag o alO zO lenO zO))))

/-- The data encrypted or decrypted, from the first counter block. -/
def oneCrypt : Prog isa := .seq (.block setData) crypt

/-- `vg_aes_gcm_seal`. -/
def «seal» : Prog isa :=
  .seq (oneEntry []) (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.block restore))))

/-- `vg_aes_gcm_open`, with `tag_len` the stack argument 9. -/
def «open» : Prog isa :=
  .seq (oneEntry (keep 9 tglO))
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov .eax (imm 0)])
      (.seq oneAad
      (.seq (oneTag uO)
      (.seq recv
      (.seq (cmp uO)
      (.seq (.block [.store (at_ .ebp auxO) .eax, .alu .test .eax (.reg .eax)])
      (.seq (.ite .e (.block []) oneCrypt)
        (.block [.mov .eax (slot auxO)]))))))))
    (.block restore)))

end VG.Impl.AesGcm.X86

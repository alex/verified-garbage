import VerifiedGarbage.TCB.AArch64.Isa

/-!
# AES-GCM: AArch64 implementation

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
* `[112, 128)`: the tag `verify` and `open` compute;
* `[128, 216)`: our caller's `x19`–`x28` and our return address `x30`;
* `[216, 256)`: arguments `seal` and `open` keep across calls;
* `[256, 288)`: the two tags compared, padded with zeros;
* `[512, 2560)`: the working space of the functions called.

A call (`bl`) stores nothing in memory, so no stack is used.

## Registers

`x19` holds `W`, `x20` the streaming state, `x21` the key context and `x22`
the number of rounds throughout; the functions called preserve them. The
pieces below (`absorb`, `crypt`, …) take their arguments in `x23` (a
pointer), `x24` (a length) and `x25` (an offset), which the callees also
preserve; `x26`–`x28` hold the lengths and the data pointer the functions
keep.

## The pieces

* `absorb yo`: GHASH, with the accumulator at `x20 + yo` and the partial
  block at `x20 + 32` holding `x25` bytes, absorbs the `x24` bytes at `x23`:
  the partial block filled first (and absorbed if full, by a call of
  `vg_ghash` on one block or on none), then whole blocks, then the last
  bytes buffered.
* `flush yo`: the `x25` buffered bytes padded with zeros, and absorbed.
* `lens yo ra rb`: the lengths block of `ra` bytes of additional data and
  `rb` bytes of text, absorbed.
* `crypt`: the `x24` bytes at `x23` XORed with the keystream, `x25` bytes
  into the current keystream block: the rest of that block (at `x20 + 64`),
  then whole blocks with `vg_aes_ctr32` from the counter block at
  `x20 + 48`, then a new keystream block for the last bytes (a call of
  `vg_aes_ctr32` on one block, or on none).
* `tag o`: the lengths block absorbed, and `GHASH ⊕ CIPH_K(J₀)` written to
  `W + o`, with `vg_aes_ctr32` on it with the counter block `J₀` (at `x20`).
* `j0`: `J₀` for the `x24`-byte nonce at `x23` (GHASH'd unless it is 12
  bytes), and the state's accumulator and first counter block `inc₃₂(J₀)`.
* `cmp`: the received tag (at `W`) and the computed one (at `W + 112`), each
  of `x28` bytes, padded with zeros and compared without a branch.

The model has no flags or register-offset addressing: the branches are
`cbz`/`cbnz` on lengths, and bytes are copied through advancing pointers.
Every call is outside any loop, and every branch is on a length or (for
`open`) on whether the tag is right: only the pointers, the lengths,
`rounds`, `tag_len` and (for `open`) whether the tag is right can affect
timing.
-/

namespace VG.Impl.AesGcm.AArch64

open VG.AArch64

/-- A function to call: its symbol and its code. -/
structure Fn where
  name : String
  code : Prog isa

/-- The implementations called: of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`. -/
structure Callees where
  ctr : Fn
  key : Fn
  gh : Fn

/-- `mov d, n`. -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- `add d, n, #k`. -/
def ptr (d n : Reg) (k : Nat) : Instr := .addImm .x d n k

/-- `mov d, #k`. -/
def imm (d : Reg) (k : Nat) : Instr := .movz .x d (BitVec.ofNat 16 k) 0

/-! ## The working space -/

def tO : Nat := 96
def uO : Nat := 112
def aadO : Nat := 216
def alenO : Nat := 224
def dataO : Nat := 232
def lenO : Nat := 240
def tlO : Nat := 248
def vO : Nat := 256
def rO : Nat := 272
def scrO : Nat := 512

/-- The registers saved at `W + 128`, `x19` (the base of the restore) last. -/
def saved : List (Reg × Nat) :=
  [(.x20, 136), (.x21, 144), (.x22, 152), (.x23, 160), (.x24, 168), (.x25, 176), (.x26, 184),
    (.x27, 192), (.x28, 200), (.x30, 208), (.x19, 128)]

/-- Saves our caller's registers at `b + 128`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str .x r b d

/-- Restores them, with `x19` (restored last) holding `W`. -/
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x19 d

/-! ## Loops -/

/-- Copies the `x13` (at least 1) bytes at `x12` to `x11`. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldrb .x14 .x12 0, .strb .x14 .x11 0, .addImm .x .x12 .x12 1,
    .addImm .x .x11 .x11 1, .subImm .x .x13 .x13 1]) (.nonzero .x .x13)

/-- Copies the `x13` bytes at `x12` to `x11`. -/
def copy : Prog isa := .ite (.zero .x .x13) (.block []) copyLoop

/-- XORs the `x13` (at least 1) bytes at `x11` into those at `x12`. -/
def xorLoop : Prog isa :=
  .loop (.block [.ldrb .x14 .x12 0, .ldrb .x15 .x11 0, .logic .eor .w .x14 .x14 .x15,
    .strb .x14 .x12 0, .addImm .x .x12 .x12 1, .addImm .x .x11 .x11 1,
    .subImm .x .x13 .x13 1]) (.nonzero .x .x13)

/-- XORs the `x13` bytes at `x11` into those at `x12`. -/
def xor : Prog isa := .ite (.zero .x .x13) (.block []) xorLoop

/-- `x10 := min (16 - x25, x24)`, for `x25 < 16`. -/
def minK : Prog isa :=
  .seq (.block [imm .x9 16, .sub .x .x9 .x9 .x25, .lsr .x .x10 .x24 4])
    (.ite (.nonzero .x .x10) (.block [mov .x10 .x9])
      (.seq (.block [.sub .x .x11 .x9 .x24, .lsr .x .x11 .x11 63])
        (.ite (.zero .x .x11) (.block [mov .x10 .x24]) (.block [mov .x10 .x9]))))

variable (c : Callees)

/-! ## GHASH -/

/-- The arguments of `vg_ghash` but the data and the number of blocks: the
hash subkey, the accumulator at `x20 + yo` and the working space. -/
def ghArgs (yo : Nat) : List Instr := [ptr .x0 .x21 240, ptr .x1 .x20 yo, ptr .x4 .x19 scrO]

def ghCall : Prog isa := .call c.gh.name c.gh.code

/-- Before the first call of `absorb`: the buffer filled from `x23`, and the
arguments for absorbing it if it is full (`x3` blocks, one or none). -/
def absSeg1 (yo : Nat) : Prog isa :=
  .seq minK
  (.seq (.block [.add .x .x11 .x20 .x25, ptr .x11 .x11 32, mov .x12 .x23, mov .x13 .x10])
  (.seq copy
  (.seq (.block [.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10, .add .x .x9 .x25 .x10,
      .subImm .x .x9 .x9 16])
  (.seq (.ite (.zero .x .x9) (.block [imm .x3 1]) (.block [imm .x3 0]))
    (.block (ghArgs yo ++ [ptr .x2 .x20 32]))))))

/-- Before the second call: the whole blocks at `x23`. -/
def absSeg2 (yo : Nat) : List Instr :=
  [.lsr .x .x3 .x24 4, mov .x2 .x23] ++ ghArgs yo ++
    [.lsl .x .x9 .x3 4, .add .x .x23 .x23 .x9, .sub .x .x24 .x24 .x9]

/-- The last `x24` bytes at `x23` buffered. -/
def absTail : Prog isa :=
  .seq (.block [ptr .x11 .x20 32, mov .x12 .x23, mov .x13 .x24]) copy

def absorb (yo : Nat) : Prog isa :=
  .seq (absSeg1 yo) (.seq (ghCall c) (.seq (.block (absSeg2 yo)) (.seq (ghCall c) absTail)))

/-- The `x25` bytes at `x12` padded with zeros in `T`, and the arguments for
absorbing `T` if they are not none. -/
def padSeg (yo : Nat) (src : List Instr) : Prog isa :=
  .seq (.block (src ++ [imm .x9 0, .str .x .x9 .x19 tO, .str .x .x9 .x19 (tO + 8), ptr .x11 .x19 tO,
      mov .x13 .x25]))
  (.seq copy
  (.seq (.ite (.zero .x .x25) (.block [imm .x3 0]) (.block [imm .x3 1]))
    (.block (ghArgs yo ++ [ptr .x2 .x19 tO]))))

/-- The `x25` buffered bytes, padded with zeros in `T`, absorbed. -/
def flush (yo : Nat) : Prog isa := .seq (padSeg yo [ptr .x12 .x20 32]) (ghCall c)

/-- The lengths block of `ra` and `rb` bytes (as `[8 ra]₆₄ ‖ [8 rb]₆₄`) in `T`. -/
def lensSeg (yo : Nat) (ra rb : Reg) : List Instr :=
  [.lsl .x .x9 ra 3, .rev .x9 .x9, .str .x .x9 .x19 tO, .lsl .x .x9 rb 3, .rev .x9 .x9,
    .str .x .x9 .x19 (tO + 8), imm .x3 1] ++ ghArgs yo ++ [ptr .x2 .x19 tO]

/-- The lengths block of `ra` and `rb` bytes, absorbed. -/
def lens (yo : Nat) (ra rb : Reg) : Prog isa := .seq (.block (lensSeg yo ra rb)) (ghCall c)

/-! ## Counter mode -/

/-- The arguments of `vg_aes_ctr32` but the data and the number of blocks. -/
def ctrArgs : List Instr := [mov .x0 .x21, mov .x1 .x22, ptr .x2 .x20 48, ptr .x5 .x19 scrO]

def ctrCall : Prog isa := .call c.ctr.name c.ctr.code

/-- The rest of the keystream block, from byte `x25` (unless it is 0), into
`x23`, and the arguments for the whole blocks after it. -/
def crSeg1 : Prog isa :=
  .seq (.ite (.zero .x .x25) (.block [imm .x10 0]) minK)
  (.seq (.block [.add .x .x11 .x20 .x25, ptr .x11 .x11 64, mov .x12 .x23, mov .x13 .x10])
  (.seq xor
    (.block ([.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10, .lsr .x .x4 .x24 4, mov .x3 .x23] ++
      ctrArgs ++ [.lsl .x .x9 .x4 4, .add .x .x23 .x23 .x9, .sub .x .x24 .x24 .x9]))))

/-- The arguments for a new keystream block (one block, if there are bytes
left, or none). -/
def crSeg2 : Prog isa :=
  .seq (.ite (.zero .x .x24) (.block [imm .x4 0])
      (.block [imm .x4 1, imm .x9 0, .str .x .x9 .x20 64, .str .x .x9 .x20 72]))
    (.block (ctrArgs ++ [ptr .x3 .x20 64]))

/-- The last `x24` bytes at `x23`, with the new keystream block. -/
def crTail : Prog isa :=
  .seq (.block [ptr .x11 .x20 64, mov .x12 .x23, mov .x13 .x24]) xor

def crypt : Prog isa :=
  .seq crSeg1 (.seq (ctrCall c) (.seq crSeg2 (.seq (ctrCall c) crTail)))

/-! ## The tag and `J₀` -/

/-- The accumulator copied to `W + o`, and the arguments for XORing
`CIPH_K(J₀)` into it. -/
def tagSeg (o : Nat) : List Instr :=
  [.ldr .x .x9 .x20 16, .str .x .x9 .x19 o, .ldr .x .x9 .x20 24, .str .x .x9 .x19 (o + 8),
    mov .x0 .x21, mov .x1 .x22, mov .x2 .x20, ptr .x3 .x19 o, imm .x4 1, ptr .x5 .x19 scrO]

/-- The tag of the lengths in `x26` and `x27` into `W + o`. -/
def tag (o : Nat) : Prog isa :=
  .seq (lens c 16 .x26 .x27) (.seq (.block (tagSeg o)) (ctrCall c))

/-- `J₀` of a 12-byte nonce: its bytes and `0x00000001` (big-endian). -/
def j012 : List Instr :=
  [.ldr .w .x9 .x23 0, .ldr .w .x10 .x23 4, .ldr .w .x11 .x23 8, .movz .w .x12 0x0100 1,
    .str .w .x9 .x20 0, .str .w .x10 .x20 4, .str .w .x11 .x20 8, .str .w .x12 .x20 12]

/-- The arguments for absorbing the whole blocks of the nonce into a zero
accumulator at `x20`, and its last `x25` bytes at `x23`. -/
def j0Seg : List Instr :=
  [imm .x9 0, .str .x .x9 .x20 0, .str .x .x9 .x20 8, .lsr .x .x3 .x24 4, mov .x2 .x23] ++ ghArgs 0 ++
    [.lsl .x .x9 .x3 4, .add .x .x23 .x23 .x9, imm .x10 15, .logic .and .x .x25 .x24 .x10]

/-- `J₀` of any other nonce, with its length in `x26` and 0 in `x27`. -/
def j0hash : Prog isa :=
  .seq (.block j0Seg) (.seq (ghCall c) (.seq (padSeg 0 [mov .x12 .x23]) (.seq (ghCall c)
    (lens c 0 .x27 .x26))))

/-- The first counter block `inc₃₂(J₀)`, and the accumulator zeroed. -/
def initState : List Instr :=
  [.ldr .w .x9 .x20 0, .ldr .w .x10 .x20 4, .ldr .w .x11 .x20 8, .ldr .w .x12 .x20 12,
    .rev32 .x12 .x12, .addImm .w .x12 .x12 1, .rev32 .x12 .x12, .str .w .x9 .x20 48,
    .str .w .x10 .x20 52, .str .w .x11 .x20 56, .str .w .x12 .x20 60, imm .x9 0,
    .str .x .x9 .x20 16, .str .x .x9 .x20 24]

/-- The streaming state for the `x24`-byte nonce at `x23` (its length also
in `x26`, and 0 in `x27`). -/
def j0 : Prog isa :=
  .seq (.block [.subImm .x .x9 .x24 12])
    (.seq (.ite (.zero .x .x9) (.block j012) (j0hash c)) (.block initState))

/-! ## Comparing tags -/

/-- The first `x28` bytes of the received tag (at `W`) and of the computed
one (at `W + 112`), padded with zeros at `W + 272` and `W + 256`, compared:
`x10` is 0 if they are equal and 1 if not (the carry of adding all ones to
their difference). -/
def cmpSeg : Prog isa :=
  .seq (.block [imm .x9 0, .str .x .x9 .x19 vO, .str .x .x9 .x19 (vO + 8), .str .x .x9 .x19 rO,
      .str .x .x9 .x19 (rO + 8), ptr .x11 .x19 rO, mov .x12 .x19, mov .x13 .x28])
  (.seq copy
  (.seq (.block [ptr .x11 .x19 vO, ptr .x12 .x19 uO, mov .x13 .x28])
  (.seq copy
    (.block [.ldr .x .x9 .x19 vO, .ldr .x .x10 .x19 rO, .logic .eor .x .x9 .x9 .x10,
      .ldr .x .x10 .x19 (vO + 8), .ldr .x .x11 .x19 (rO + 8), .logic .eor .x .x10 .x10 .x11,
      .logic .orr .x .x9 .x9 .x10, imm .x11 0, .subImm .x .x12 .x11 1, .adds .x .x9 .x9 .x12,
      .adcs .x .x10 .x11 .x11]))))

/-- `x9 := 1` if `x28` is `k`. -/
def tlTest (k : Nat) : Prog isa :=
  .seq (.block [.subImm .x .x10 .x28 k]) (.ite (.zero .x .x10) (.block [imm .x9 1]) (.block []))

/-- `x9` is 1 if the tag length `x28` is one §5.2.1.2 allows (4, 8 or 12 to
16), and 0 if not. -/
def tagLenOk : Prog isa :=
  .seq (.block [imm .x9 0])
    (.seq (tlTest 4) (.seq (tlTest 8) (.seq (tlTest 12) (.seq (tlTest 13) (.seq (tlTest 14)
      (.seq (tlTest 15) (tlTest 16)))))))

/-! ## The functions -/

/-- `vg_aes_gcm_init(key = x0, key_len = x1, ctx = x2, scratch = x3)`. -/
def initSeg1 : List Instr :=
  save .x3 ++ [mov .x19 .x3, mov .x21 .x2, .lsr .x .x22 .x1 2, .addImm .x .x22 .x22 6,
    ptr .x3 .x19 scrO]

def initSeg2 : List Instr :=
  [imm .x9 0, .str .x .x9 .x21 240, .str .x .x9 .x21 248, .str .x .x9 .x19 tO,
    .str .x .x9 .x19 (tO + 8), mov .x0 .x21, mov .x1 .x22, ptr .x2 .x19 tO, ptr .x3 .x21 240,
    imm .x4 1, ptr .x5 .x19 scrO]

def init : Prog isa :=
  .seq (.block initSeg1)
  (.seq (.call c.key.name c.key.code)
  (.seq (.block initSeg2)
  (.seq (ctrCall c)
    (.block restore))))

/-- `vg_aes_gcm_stream_init(ctx = x0, nonce = x1, nonce_len = x2, state = x3, scratch = x4)`. -/
def siEntry : List Instr :=
  save .x4 ++ [mov .x19 .x4, mov .x20 .x3, mov .x21 .x0, mov .x23 .x1, mov .x24 .x2, mov .x26 .x2,
    imm .x27 0]

def streamInit : Prog isa := .seq (.block siEntry) (.seq (j0 c) (.block restore))

/-- `vg_aes_gcm_stream_aad(ctx = x0, state = x1, aad_len = x2, data = x3, len = x4, scratch = x5)`. -/
def aadEntry : List Instr :=
  save .x5 ++ [mov .x19 .x5, mov .x20 .x1, mov .x21 .x0, mov .x23 .x3, mov .x24 .x4, imm .x9 15,
    .logic .and .x .x25 .x2 .x9]

def streamAad : Prog isa := .seq (.block aadEntry) (.seq (absorb c 16) (.block restore))

/-- The entry of `encrypt` and `decrypt`: `(ctx = x0, rounds = x1, state = x2,
aad_len = x3, text_len = x4, data = x5, len = x6, scratch = x7)`: `x26` the
length, `x27` the text so far and `x28` the data, and `aad_len mod 16` in
`x25`. -/
def crEntry : List Instr :=
  save .x7 ++ [mov .x19 .x7, mov .x20 .x2, mov .x21 .x0, mov .x22 .x1, mov .x26 .x6, mov .x27 .x4,
    mov .x28 .x5, imm .x9 15, .logic .and .x .x25 .x3 .x9]

/-- What `flush` pads: the buffered additional data (`x25`) before the first
text, nothing otherwise. -/
def fo : Prog isa :=
  .ite (.zero .x .x26) (.block [imm .x25 0])
    (.ite (.zero .x .x27) (.block []) (.block [imm .x25 0]))

/-- The offset into the text, and the text as the piece to absorb or crypt. -/
def textArgs : List Instr := [imm .x9 15, .logic .and .x .x25 .x27 .x9, mov .x23 .x28, mov .x24 .x26]

/-- The text absorbed into GHASH, if there is any. -/
def textAbs : Prog isa := .ite (.zero .x .x26) (.block []) (absorb c 16)

/-- The additional data padded if this is the first text, and the text
(`x26` bytes at `x28`, after `x27` bytes) encrypted and absorbed. -/
def encBody : Prog isa :=
  .seq fo (.seq (flush c 16) (.seq (.block textArgs) (.seq (crypt c)
    (.seq (.block [mov .x23 .x28, mov .x24 .x26]) (textAbs c)))))

/-- The additional data padded if this is the first text, and the text
absorbed. -/
def decAbs : Prog isa :=
  .seq fo (.seq (flush c 16) (.seq (.block textArgs) (textAbs c)))

/-- `decAbs`, and the text decrypted. -/
def decBody : Prog isa :=
  .seq (decAbs c) (.seq (.block [mov .x23 .x28, mov .x24 .x26]) (crypt c))

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa := .seq (.block crEntry) (.seq (encBody c) (.block restore))

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa := .seq (.block crEntry) (.seq (decBody c) (.block restore))

/-- The entry of `finish` and `verify`: `(ctx = x0, rounds = x1, state = x2,
aad_len = x3, text_len = x4, work = x5)`. -/
def finEntry : List Instr :=
  save .x5 ++ [mov .x19 .x5, mov .x20 .x2, mov .x21 .x0, mov .x22 .x1, mov .x26 .x3, mov .x27 .x4]

/-- The buffered bytes (of the text, or of the additional data if there is
no text) padded and absorbed, and the tag into `W + o`. -/
def finBody (o : Nat) : Prog isa :=
  .seq (.ite (.zero .x .x27) (.block [imm .x9 15, .logic .and .x .x25 .x26 .x9])
      (.block [imm .x9 15, .logic .and .x .x25 .x27 .x9]))
    (.seq (flush c 16) (tag c o))

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinish : Prog isa := .seq (.block finEntry) (.seq (finBody c 0) (.block restore))

/-- The computed tag (at `W + 112`) to `W`, if it is equal to the received
one (`x10` is 0), else zeros; `x0` is 1 if they are equal, 0 if not. -/
def verMask : List Instr :=
  [.subImm .x .x11 .x10 1, .ldr .x .x9 .x19 uO, .logic .and .x .x9 .x9 .x11, .str .x .x9 .x19 0,
    .ldr .x .x9 .x19 (uO + 8), .logic .and .x .x9 .x9 .x11, .str .x .x9 .x19 8, imm .x0 1,
    .sub .x .x0 .x0 .x10]

/-- `vg_aes_gcm_stream_verify`, with `tag_len = x6`. -/
def streamVerify : Prog isa :=
  .seq (.block (finEntry ++ [mov .x28 .x6]))
  (.seq tagLenOk
  (.seq (.ite (.zero .x .x9) (.block [imm .x9 0, .str .x .x9 .x19 0, .str .x .x9 .x19 8, imm .x0 0])
      (.seq (finBody c uO) (.seq cmpSeg (.block verMask))))
    (.block restore)))

/-- The entry of `seal` and `open`: `(ctx = x0, rounds = x1, nonce = x2,
nonce_len = x3, aad = x4, aad_len = x5, data = x6, len = x7, work = [sp])`.
The state is at `W + 16`. -/
def oneEntry : List Instr :=
  [.ldrSp .x9 0] ++ save .x9 ++
    [mov .x19 .x9, ptr .x20 .x19 16, mov .x21 .x0, mov .x22 .x1, .str .x .x4 .x19 aadO,
      .str .x .x5 .x19 alenO, .str .x .x6 .x19 dataO, .str .x .x7 .x19 lenO, mov .x23 .x2,
      mov .x24 .x3, mov .x26 .x3, imm .x27 0]

/-- The additional data absorbed. -/
def oneAad : Prog isa :=
  .seq (.block [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO, imm .x25 0]) (absorb c 16)

/-- The arguments of `encBody` and `decAbs`: no text yet. -/
def encPrep : List Instr :=
  [.ldr .x .x9 .x19 alenO, imm .x10 15, .logic .and .x .x25 .x9 .x10, .ldr .x .x26 .x19 lenO,
    imm .x27 0, .ldr .x .x28 .x19 dataO]

/-- The arguments of `finBody`: the lengths. -/
def finPrep : List Instr := [.ldr .x .x26 .x19 alenO, .ldr .x .x27 .x19 lenO]

/-- `vg_aes_gcm_seal`. -/
def «seal» : Prog isa :=
  .seq (.block oneEntry)
  (.seq (j0 c)
  (.seq (oneAad c)
  (.seq (.block encPrep)
  (.seq (encBody c)
  (.seq (.block finPrep)
  (.seq (finBody c 0)
    (.block restore)))))))

/-- The text decrypted, from the first counter block. -/
def oneCrypt : Prog isa :=
  .seq (.block [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0]) (crypt c)

/-- `open` once the tag length is allowed. -/
def openMain : Prog isa :=
  .seq (j0 c)
  (.seq (oneAad c)
  (.seq (.block encPrep)
  (.seq (decAbs c)
  (.seq (.block finPrep)
  (.seq (finBody c uO)
  (.seq (.block [.ldr .x .x28 .x19 tlO])
  (.seq cmpSeg
  (.seq (.block [imm .x27 1, .sub .x .x27 .x27 .x10])
  (.seq (.ite (.zero .x .x27) (.block []) (oneCrypt c))
    (.block [mov .x0 .x27]))))))))))

/-- `vg_aes_gcm_open`, with `tag_len = [sp + 8]`. -/
def «open» : Prog isa :=
  .seq (.block (oneEntry ++ [.ldrSp .x10 8, .str .x .x10 .x19 tlO, mov .x28 .x10]))
  (.seq tagLenOk
  (.seq (.ite (.zero .x .x9) (.block [imm .x0 0]) (openMain c))
    (.block restore)))

end VG.Impl.AesGcm.AArch64

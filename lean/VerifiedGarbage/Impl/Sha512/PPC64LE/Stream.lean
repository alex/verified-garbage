import VerifiedGarbage.Impl.Sha512.PPC64LE

/-!
# Streaming SHA-512: PPC64LE implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`).

* `init iv (state = r3)` stores the initial hash value `iv`.
* `update(state = r3, count = r4, data = r5, len = r6, scratch = r7)`
  processes one block per iteration: straight from `data` while the buffer is
  empty and a whole block remains, otherwise by copying bytes into the buffer,
  compressing it once it is full.
* `finalize(state = r3, count = r4, out = r5, scratch = r6)` pads the
  buffered bytes (one or two blocks), compresses them and writes the final
  hash value.

The compression function's code (`Impl.Sha512.PPC64LE.compress`) is inlined,
as on AArch64, with `scratch[0..176)` as its scratch space, so no function
is called and the link register is never changed: there is no stack frame.
Its `Verified` proof guarantees that it preserves `r14`–`r31` (it only
writes `r14`–`r19` after saving them), so our own variables live in
`r26`–`r31` (`r26` = `state`, `r27` = `scratch`), and our caller's values of
those registers are saved in `scratch[176..224)`.

As in the SHA-256 implementation, byte `r` of the buffer is addressed as
`64(r11)` with `r11 = state + r`, `data` is consumed through a pointer that
advances, and every comparison is a shift (`len ≥ 128` iff `len >> 7 ≠ 0`)
or a subtraction tested against zero. Every address and branch depends only
on the pointers, `count` and `len`.
-/

namespace VG.Impl.Sha512.PPC64LE.Stream

open VG.PPC64LE
open VG.Impl.Sha512.PPC64LE (compress movImm64)

/-- `mr d, n` (as `addi d, n, 0`; `n` is not `r0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k => movImm64 .r8 iv[k]! ++ [.store .d .r8 .r3 (8 * k)])

/-- The nonvolatile registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r26, 176), (.r27, 184), (.r28, 192), (.r29, 200), (.r30, 208), (.r31, 216)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store .d r b d

/-- Restore them from `scratch` in `r27` (`r27`, the base, last). -/
def restore : List Instr :=
  (saved.filter (·.1 != .r27)).map (fun (r, d) => .load .d r .r27 d) ++ [.load .d .r27 .r27 184]

/-- Compress the block at `r4` into the hash value at `r26`, with scratch
space `r27`. -/
def compressAt : Prog isa :=
  .seq (.block [mov .r3 .r26, .li .r5 1, mov .r6 .r27]) compress

/-! ## `update`

Registers: `r28` = `data`, `r29` = bytes of `data` left, `r30` = bytes in the
buffer (`r`), `r9` = whether this iteration compresses a block (at `r4`).
The loop runs while `r29 ≠ 0`, so each iteration starts with `r29 ≥ 1` and
`r30 < 128`. -/

/-- A whole block straight from `data`. -/
def direct : List Instr :=
  [mov .r4 .r28, .addi .r28 .r28 128, .subi .r29 .r29 128, .li .r9 1]

/-- Copy `n = min(128 - r, len) ≥ 1` bytes of `data` into the buffer; if that
fills it, compress it. -/
def fill : Prog isa :=
  -- r10 := 128 - r; if len < 128 and len + r < 128 (i.e. len < 128 - r), r10 := len.
  .seq (.block [.li .r10 128, .sub .r10 .r10 .r30, .lsr .d .r8 .r29 7])
  (.seq (.ite (.zero .d .r8)
      (.seq (.block [.add .r8 .r29 .r30, .lsr .d .r8 .r8 7])
        (.ite (.zero .d .r8) (.block [mov .r10 .r29]) (.block [])))
      (.block []))
  (.seq (.block [.sub .r29 .r29 .r10])
  (.seq (.loop (.block [.lbz .r8 .r28 0, .add .r11 .r26 .r30, .stb .r8 .r11 64,
      .addi .r28 .r28 1, .addi .r30 .r30 1, .subi .r10 .r10 1]) (.nonzero .d .r10))
  -- Full: compress the buffer.
  (.seq (.block [.subi .r8 .r30 128])
    (.ite (.zero .d .r8) (.block [.addi .r4 .r26 64, .li .r30 0, .li .r9 1])
      (.block []))))))

def updateBody : Prog isa :=
  .seq (.block [.li .r9 0])
  (.seq (.ite (.zero .d .r30)
      (.seq (.block [.lsr .d .r8 .r29 7]) (.ite (.zero .d .r8) fill (.block direct)))
      fill)
    (.ite (.zero .d .r9) (.block []) compressAt))

def update : Prog isa :=
  .seq (.block (save .r7 ++ [mov .r26 .r3, mov .r27 .r7, mov .r28 .r5, mov .r29 .r6,
      .li .r8 127, .logic .and .r30 .r4 .r8]))
  (.seq (.ite (.zero .d .r29) (.block []) (.loop updateBody (.nonzero .d .r29)))
    (.block restore))

/-! ## `finalize`

Registers: `r28` = `out`, `r29` = `count`, `r30` = bytes in the buffer (`r`),
`r31` = 1 while the block being padded is not the last one (then 0). -/

def finalizeBody : Prog isa :=
  -- Zero the buffer from `r` to 128, or to 112 in the last block.
  .seq (.block [.li .r10 128])
  (.seq (.ite (.zero .d .r31) (.block [.li .r10 112]) (.block []))
  (.seq (.block [.li .r8 0, .sub .r10 .r10 .r30])
  (.seq (.ite (.zero .d .r10) (.block [])
      (.loop (.block [.add .r11 .r26 .r30, .stb .r8 .r11 64, .addi .r30 .r30 1,
        .subi .r10 .r10 1]) (.nonzero .d .r10)))
  -- In the last block, the message length in bits as a 128-bit big-endian
  -- integer: `count >> 61`, then `count << 3` (modulo 2⁶⁴).
  (.seq (.ite (.zero .d .r31)
      (.block [.lsr .d .r8 .r29 61, .li .r11 176, .storeRev .d .r8 .r26 .r11,
        .add .r8 .r29 .r29, .add .r8 .r8 .r8, .add .r8 .r8 .r8, .li .r11 184,
        .storeRev .d .r8 .r26 .r11])
      (.block []))
  (.seq (.block [.addi .r4 .r26 64])
  (.seq compressAt
    (.block [.li .r30 0, .subi .r31 .r31 1])))))))

def finalize : Prog isa :=
  .seq (.block (save .r6 ++ [mov .r26 .r3, mov .r27 .r6, mov .r28 .r5, mov .r29 .r4,
      .li .r8 127, .logic .and .r30 .r29 .r8,
      -- The `0x80` byte.
      .li .r8 0x80, .add .r11 .r26 .r30, .stb .r8 .r11 64, .addi .r30 .r30 1,
      -- Two blocks iff that leaves fewer than 16 bytes for the length (r ≥ 113).
      .addi .r31 .r30 15, .lsr .d .r31 .r31 7]))
  (.seq (.loop finalizeBody (.zero .d .r31))
    (.block ((List.range 8).flatMap (fun k =>
        [.load .d .r8 .r26 (8 * k), .li .r11 (8 * k), .storeRev .d .r8 .r28 .r11]) ++
      restore)))

end VG.Impl.Sha512.PPC64LE.Stream

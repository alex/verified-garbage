import VerifiedGarbage.Impl.Sha256.AArch64

/-!
# Streaming SHA-256: AArch64 implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha256.Repr`).

* `init(state = x0)` stores `H⁽⁰⁾`.
* `update(state = x0, count = x1, data = x2, len = x3, scratch = x4)`
  processes one block per iteration: straight from `data` while the buffer is
  empty and a whole block remains, otherwise by copying bytes into the buffer,
  compressing it once it is full.
* `finalize(state = x0, count = x1, out = x2, scratch = x3)` pads the
  buffered bytes (one or two blocks), compresses them and writes the digest.

The compression function's code (`Impl.Sha256.AArch64.compress`) is inlined
with `scratch[0..112)` as its scratch space. It only uses `x0`–`x15`, and its
`Verified` proof guarantees that it preserves `x19`–`x28`, so our own
variables live there (`x19` = `state`, `x20` = `scratch`), and our caller's
values of those registers are saved in `scratch[112..160)`.

The model has no register-offset addressing, so byte `r` of the buffer is
addressed as `[x12, #32]` with `x12 = state + r` computed just before the
access, and `data` is consumed through a pointer that advances. It has no
flags either: every comparison is a shift (`len ≥ 64` iff `len >> 6 ≠ 0`)
or a subtraction tested with `cbz`/`cbnz`. Every address and branch depends
only on the pointers, `count` and `len`.
-/

namespace VG.Impl.Sha256.AArch64.Stream

open VG.AArch64
open VG.Impl.Sha256.AArch64 (compress)

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

def init : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.movz .w .x9 (Spec.Sha256.H0[k]!.extractLsb' 0 16) 0,
     .movk .w .x9 (Spec.Sha256.H0[k]!.extractLsb' 16 16) 1,
     .str .w .x9 .x0 (4 * k)])

/-- The callee-saved registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.x19, 112), (.x20, 120), (.x21, 128), (.x22, 136), (.x23, 144), (.x24, 152)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str .x r b d

/-- Restore them from `scratch` in `x20` (`x20`, the base, last). -/
def restore : List Instr :=
  (saved.filter (·.1 != .x20)).map (fun (r, d) => .ldr .x r .x20 d) ++ [.ldr .x .x20 .x20 120]

/-- Compress the block at `x1` into the hash value at `x19`, with scratch
space `x20`. -/
def compressAt : Prog isa :=
  .seq (.block [mov .x0 .x19, .movz .x .x2 1 0, mov .x3 .x20]) compress

/-! ## `update`

Registers: `x21` = `data`, `x22` = bytes of `data` left, `x23` = bytes in the
buffer (`r`), `x10` = whether this iteration compresses a block (at `x1`).
The loop runs while `x22 ≠ 0`, so each iteration starts with `x22 ≥ 1` and
`x23 < 64`. -/

/-- A whole block straight from `data`. -/
def direct : List Instr :=
  [mov .x1 .x21, .addImm .x .x21 .x21 64, .subImm .x .x22 .x22 64, .movz .x .x10 1 0]

/-- Copy `n = min(64 - r, len) ≥ 1` bytes of `data` into the buffer; if that
fills it, compress it. -/
def fill : Prog isa :=
  -- x11 := 64 - r; if len < 64 and len + r < 64 (i.e. len < 64 - r), x11 := len.
  .seq (.block [.movz .x .x11 64 0, .sub .x .x11 .x11 .x23, .lsr .x .x9 .x22 6])
  (.seq (.ite (.zero .x .x9)
      (.seq (.block [.add .x .x9 .x22 .x23, .lsr .x .x9 .x9 6])
        (.ite (.zero .x .x9) (.block [mov .x11 .x22]) (.block [])))
      (.block []))
  (.seq (.block [.sub .x .x22 .x22 .x11])
  (.seq (.loop (.block [.ldrb .x9 .x21 0, .add .x .x12 .x19 .x23, .strb .x9 .x12 32,
      .addImm .x .x21 .x21 1, .addImm .x .x23 .x23 1, .subImm .x .x11 .x11 1]) (.nonzero .x .x11))
  -- Full: compress the buffer.
  (.seq (.block [.subImm .x .x9 .x23 64])
    (.ite (.zero .x .x9) (.block [.addImm .x .x1 .x19 32, .movz .x .x23 0 0, .movz .x .x10 1 0])
      (.block []))))))

def updateBody : Prog isa :=
  .seq (.block [.movz .x .x10 0 0])
  (.seq (.ite (.zero .x .x23)
      (.seq (.block [.lsr .x .x9 .x22 6]) (.ite (.zero .x .x9) fill (.block direct)))
      fill)
    (.ite (.zero .x .x10) (.block []) compressAt))

def update : Prog isa :=
  .seq (.block (save .x4 ++ [mov .x19 .x0, mov .x20 .x4, mov .x21 .x2, mov .x22 .x3,
      .movz .x .x9 63 0, .logic .and .x .x23 .x1 .x9]))
  (.seq (.ite (.zero .x .x22) (.block []) (.loop updateBody (.nonzero .x .x22)))
    (.block restore))

/-! ## `finalize`

Registers: `x21` = `out`, `x22` = `count`, `x23` = bytes in the buffer (`r`),
`x24` = 1 while the block being padded is not the last one (then 0). -/

def finalizeBody : Prog isa :=
  -- Zero the buffer from `r` to 64, or to 56 in the last block.
  .seq (.block [.movz .x .x11 64 0])
  (.seq (.ite (.zero .x .x24) (.block [.movz .x .x11 56 0]) (.block []))
  (.seq (.block [.movz .x .x9 0 0, .sub .x .x11 .x11 .x23])
  (.seq (.ite (.zero .x .x11) (.block [])
      (.loop (.block [.add .x .x12 .x19 .x23, .strb .x9 .x12 32, .addImm .x .x23 .x23 1,
        .subImm .x .x11 .x11 1]) (.nonzero .x .x11)))
  -- In the last block, the message length in bits (`8 * count`), big-endian.
  (.seq (.ite (.zero .x .x24)
      (.block [.add .x .x9 .x22 .x22, .add .x .x9 .x9 .x9, .add .x .x9 .x9 .x9, .rev .x9 .x9,
        .str .x .x9 .x19 88])
      (.block []))
  (.seq (.block [.addImm .x .x1 .x19 32])
  (.seq compressAt
    (.block [.movz .x .x23 0 0, .subImm .x .x24 .x24 1])))))))

def finalize : Prog isa :=
  .seq (.block (save .x3 ++ [mov .x19 .x0, mov .x20 .x3, mov .x21 .x2, mov .x22 .x1,
      .movz .x .x9 63 0, .logic .and .x .x23 .x22 .x9,
      -- The `0x80` byte.
      .movz .x .x9 0x80 0, .add .x .x12 .x19 .x23, .strb .x9 .x12 32, .addImm .x .x23 .x23 1,
      -- Two blocks iff that leaves fewer than 8 bytes for the length (r ≥ 57).
      .addImm .x .x24 .x23 7, .lsr .x .x24 .x24 6]))
  (.seq (.loop finalizeBody (.zero .x .x24))
    (.block ((List.range 8).flatMap (fun k =>
        [.ldr .w .x9 .x19 (4 * k), .rev32 .x9 .x9, .str .w .x9 .x21 (4 * k)]) ++
      restore)))

end VG.Impl.Sha256.AArch64.Stream

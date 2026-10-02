import VerifiedGarbage.Impl.Sha512.AArch64

/-!
# Streaming SHA-512: AArch64 implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`).

* `init iv (state = x0)` stores the initial hash value `iv`.
* `update(state = x0, count = x1, data = x2, len = x3, scratch = x4)`
  processes one block per iteration: straight from `data` while the buffer is
  empty and a whole block remains, otherwise by copying bytes into the buffer,
  compressing it once it is full.
* `finalize(state = x0, count = x1, out = x2, scratch = x3)` pads the
  buffered bytes (one or two blocks), compresses them and writes the final
  hash value.

The compression function's code (`Impl.Sha512.AArch64.compress`) is inlined
with `scratch[0..640)` as its scratch space. It only uses `x0`–`x15`, and its
`Verified` proof guarantees that it preserves `x19`–`x28`, so our own
variables live there (`x19` = `state`, `x20` = `scratch`), and our caller's
values of those registers are saved in `scratch[640..688)`.

As in the SHA-256 implementation, byte `r` of the buffer is addressed as
`[x12, #64]` with `x12 = state + r`, `data` is consumed through a pointer that
advances, and every comparison is a shift (`len ≥ 128` iff `len >> 7 ≠ 0`) or
a subtraction tested with `cbz`/`cbnz`. Every address and branch depends only
on the pointers, `count` and `len`.
-/

namespace VG.Impl.Sha512.AArch64.Stream

open VG.AArch64
open VG.Impl.Sha512.AArch64 (compress movImm64)

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k => movImm64 .x9 iv[k]! ++ [.str .x .x9 .x0 (8 * k)])

/-- The callee-saved registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.x19, 640), (.x20, 648), (.x21, 656), (.x22, 664), (.x23, 672), (.x24, 680)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str .x r b d

/-- Restore them from `scratch` in `x20` (`x20`, the base, last). -/
def restore : List Instr :=
  (saved.filter (·.1 != .x20)).map (fun (r, d) => .ldr .x r .x20 d) ++ [.ldr .x .x20 .x20 648]

/-- Compress the block at `x1` into the hash value at `x19`, with scratch
space `x20`. -/
def compressAtWith (code : Prog isa) : Prog isa :=
  .seq (.block [mov .x0 .x19, .movz .x .x2 1 0, mov .x3 .x20]) code

/-! ## `update`

Registers: `x21` = `data`, `x22` = bytes of `data` left, `x23` = bytes in the
buffer (`r`), `x10` = whether this iteration compresses a block (at `x1`).
The loop runs while `x22 ≠ 0`, so each iteration starts with `x22 ≥ 1` and
`x23 < 128`. -/

/-- A whole block straight from `data`. -/
def direct : List Instr :=
  [mov .x1 .x21, .addImm .x .x21 .x21 128, .subImm .x .x22 .x22 128, .movz .x .x10 1 0]

/-- Copy `n = min(128 - r, len) ≥ 1` bytes of `data` into the buffer; if that
fills it, compress it. -/
def fill : Prog isa :=
  -- x11 := 128 - r; if len < 128 and len + r < 128 (i.e. len < 128 - r), x11 := len.
  .seq (.block [.movz .x .x11 128 0, .sub .x .x11 .x11 .x23, .lsr .x .x9 .x22 7])
  (.seq (.ite (.zero .x .x9)
      (.seq (.block [.add .x .x9 .x22 .x23, .lsr .x .x9 .x9 7])
        (.ite (.zero .x .x9) (.block [mov .x11 .x22]) (.block [])))
      (.block []))
  (.seq (.block [.sub .x .x22 .x22 .x11])
  (.seq (.loop (.block [.ldrb .x9 .x21 0, .add .x .x12 .x19 .x23, .strb .x9 .x12 64,
      .addImm .x .x21 .x21 1, .addImm .x .x23 .x23 1, .subImm .x .x11 .x11 1]) (.nonzero .x .x11))
  -- Full: compress the buffer.
  (.seq (.block [.subImm .x .x9 .x23 128])
    (.ite (.zero .x .x9) (.block [.addImm .x .x1 .x19 64, .movz .x .x23 0 0, .movz .x .x10 1 0])
      (.block []))))))

def updateBodyWith (code : Prog isa) : Prog isa :=
  .seq (.block [.movz .x .x10 0 0])
  (.seq (.ite (.zero .x .x23)
      (.seq (.block [.lsr .x .x9 .x22 7]) (.ite (.zero .x .x9) fill (.block direct)))
      fill)
    (.ite (.zero .x .x10) (.block []) (compressAtWith code)))

def updateWith (code : Prog isa) : Prog isa :=
  .seq (.block (save .x4 ++ [mov .x19 .x0, mov .x20 .x4, mov .x21 .x2, mov .x22 .x3,
      .movz .x .x9 127 0, .logic .and .x .x23 .x1 .x9]))
  (.seq (.ite (.zero .x .x22) (.block []) (.loop (updateBodyWith code) (.nonzero .x .x22)))
    (.block restore))

/-! ## `finalize`

Registers: `x21` = `out`, `x22` = `count`, `x23` = bytes in the buffer (`r`),
`x24` = 1 while the block being padded is not the last one (then 0). -/

def finalizeBodyWith (code : Prog isa) : Prog isa :=
  -- Zero the buffer from `r` to 128, or to 112 in the last block.
  .seq (.block [.movz .x .x11 128 0])
  (.seq (.ite (.zero .x .x24) (.block [.movz .x .x11 112 0]) (.block []))
  (.seq (.block [.movz .x .x9 0 0, .sub .x .x11 .x11 .x23])
  (.seq (.ite (.zero .x .x11) (.block [])
      (.loop (.block [.add .x .x12 .x19 .x23, .strb .x9 .x12 64, .addImm .x .x23 .x23 1,
        .subImm .x .x11 .x11 1]) (.nonzero .x .x11)))
  -- In the last block, the message length in bits as a 128-bit big-endian
  -- integer: `count >> 61`, then `count << 3` (modulo 2⁶⁴).
  (.seq (.ite (.zero .x .x24)
      (.block [.lsr .x .x9 .x22 61, .rev .x9 .x9, .str .x .x9 .x19 176,
        .add .x .x9 .x22 .x22, .add .x .x9 .x9 .x9, .add .x .x9 .x9 .x9, .rev .x9 .x9,
        .str .x .x9 .x19 184])
      (.block []))
  (.seq (.block [.addImm .x .x1 .x19 64])
  (.seq (compressAtWith code)
    (.block [.movz .x .x23 0 0, .subImm .x .x24 .x24 1])))))))

def finalizeWith (code : Prog isa) : Prog isa :=
  .seq (.block (save .x3 ++ [mov .x19 .x0, mov .x20 .x3, mov .x21 .x2, mov .x22 .x1,
      .movz .x .x9 127 0, .logic .and .x .x23 .x22 .x9,
      -- The `0x80` byte.
      .movz .x .x9 0x80 0, .add .x .x12 .x19 .x23, .strb .x9 .x12 64, .addImm .x .x23 .x23 1,
      -- Two blocks iff that leaves fewer than 16 bytes for the length (r ≥ 113).
      .addImm .x .x24 .x23 15, .lsr .x .x24 .x24 7]))
  (.seq (.loop (finalizeBodyWith code) (.zero .x .x24))
    (.block ((List.range 8).flatMap (fun k =>
        [.ldr .x .x9 .x19 (8 * k), .rev .x9 .x9, .str .x .x9 .x21 (8 * k)]) ++
      restore)))

def compressAt : Prog isa := compressAtWith compress
def updateBody : Prog isa := updateBodyWith compress
def update : Prog isa := updateWith compress
def finalizeBody : Prog isa := finalizeBodyWith compress
def finalize : Prog isa := finalizeWith compress

end VG.Impl.Sha512.AArch64.Stream

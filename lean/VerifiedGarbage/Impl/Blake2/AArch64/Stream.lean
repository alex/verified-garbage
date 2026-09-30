import VerifiedGarbage.Impl.Blake2.AArch64

/-!
# Streaming BLAKE2: AArch64 implementation

`init`, `update` and `finalize` for words of `w` bits (`Spec.Blake2.b` or
`Spec.Blake2.s`), on the streaming state of `Spec.Blake2.Repr`, as on x86-64
(`Impl/Blake2/X86_64/Stream.lean`): the hash value (`N = 8 · w/8` bytes)
followed by a `B`-byte buffer (`B = 16 · w/8`) holding the last block of the
data so far, 1 to `B` bytes of it (none for empty data). The caller keeps the
byte count, `count`, from which the number of buffered bytes follows.

* `init(state = x0, outlen = x1, key = x2, keylen = x3)` stores the initial
  hash value and, for a key, the key block in the buffer.
* `update(state = x0, count = x1, data = x2, len = x3, scratch = x4)` fills
  the buffer; if more data follows, compresses it, compresses every block of
  `data` but the last straight from `data`, and copies that last one (1 to
  `B` bytes) to the buffer.
* `finalize(state = x0, count = x1, out = x2, scratch = x3)` pads the
  buffered block with zeros, compresses it as the last block, and writes the
  hash value to `out`.

The compression function (`compress`, `Impl/Blake2/AArch64.lean`) is called
with `scratch` as its scratch space; it never writes `x19`–`x24`, so our own
variables live there (`x19` = `state`, `x20` = `scratch`, `x21` = `data` or
`out`, `x22` = bytes of `data` left, `x23` = bytes in the buffer, `x24` =
the byte count), and our caller's values of those registers are saved in
`scratch[512..560)`. Our return address (`x30`), which each call replaces, is
saved in a stack frame around the whole function.

The model has no register-offset addressing, so byte `r` of the buffer is
addressed as `[x12, #N]` with `x12 = state + r` computed just before the
access, and `data` is consumed through a pointer that advances. It has no
flags either: every comparison is a shift or a subtraction tested with
`cbz`/`cbnz`. Every address and branch depends only on the pointers, `count`,
`len`, `outlen` and `keylen`.
-/

namespace VG.Impl.Blake2.AArch64.Stream

open VG.AArch64
open VG.Impl.Blake2.AArch64 (sz ws lbb movImm64 compress)

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

section
variable (w : Nat)

/-- The size of the hash value, where the buffer starts. -/
def N : Nat := 8 * ws w
/-- The block size. -/
def B : Nat := 16 * ws w

end

/-- The callee-saved registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.x19, 512), (.x20, 520), (.x21, 528), (.x22, 536), (.x23, 544), (.x24, 552)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str .x r b d

/-- Restore them from `scratch` in `x20` (`x20`, the base, last). -/
def restore : List Instr :=
  [.ldr .x .x19 .x20 512, .ldr .x .x21 .x20 528, .ldr .x .x22 .x20 536,
    .ldr .x .x23 .x20 544, .ldr .x .x24 .x20 552, .ldr .x .x20 .x20 520]

section
variable {w : Nat} (P : Spec.Blake2.Params w)

/-- `x23` := the number of bytes in the buffer for the byte count in `x24`:
`((count - 1) mod B) + 1`, or 0 if `count = 0`. -/
def bufLen : Prog isa :=
  .seq (.block [.subImm .x .x23 .x24 1, .movz .x .x9 (BitVec.ofNat 16 (B w - 1)) 0,
      .logic .and .x .x23 .x23 .x9, .addImm .x .x23 .x23 1])
    (.ite (.zero .x .x24) (.block [.movz .x .x23 0 0]) (.block []))

/-- Compress into the hash value at `x19`, with scratch space `x20`, after
`args` set the blocks (`x1`), their number (`x2`), the counter (`x3`) and the
final block flag (`x4`). -/
def compressWith (args : List Instr) : Prog isa :=
  .seq (.block ([mov .x0 .x19] ++ args ++ [mov .x5 .x20]))
    (.call (if w = 64 then "vg_blake2b_compress" else "vg_blake2s_compress") (compress P))

/-- The loop copying `x11 ≥ 1` bytes of `data` (at `x21`) to the buffer, from
byte `x23` on. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldrb .x9 .x21 0, .add .x .x12 .x19 .x23, .strb .x9 .x12 (N w),
    .addImm .x .x21 .x21 1, .addImm .x .x23 .x23 1, .subImm .x .x11 .x11 1]) (.nonzero .x .x11)

/-! ## `update` -/

/-- Copy `min(B - x23, x22)` bytes of `data` to the buffer: `x11 := B - x23`,
and if `x22 < B` and `x22 + x23 < B` (i.e. `x22 < B - x23`), `x11 := x22`. -/
def fill : Prog isa :=
  .seq (.block [.movz .x .x11 (BitVec.ofNat 16 (B w)) 0, .sub .x .x11 .x11 .x23,
      .lsr .x .x9 .x22 (lbb w)])
  (.seq (.ite (.zero .x .x9)
      (.seq (.block [.add .x .x9 .x22 .x23, .lsr .x .x9 .x9 (lbb w)])
        (.ite (.zero .x .x9) (.block [mov .x11 .x22]) (.block [])))
      (.block []))
  (.seq (.block [.sub .x .x22 .x22 .x11, .add .x .x24 .x24 .x11])
    (.ite (.zero .x .x11) (.block []) (copyLoop (w := w)))))

/-- Compress the (full) buffer, which is not the last block: its counter is
the byte count. -/
def compressBuf : Prog isa :=
  .seq (compressWith P [.addImm .x .x1 .x19 (N w), .movz .x .x2 1 0, mov .x3 .x24, .movz .x .x4 0 0])
    (.block [.movz .x .x23 0 0])

/-- If the buffer is not empty: fill it, and if more data follows, compress
it. -/
def head : Prog isa :=
  .ite (.zero .x .x23) (.block [])
    (.seq (fill (w := w)) (.ite (.zero .x .x22) (.block []) (compressBuf P)))

/-- With the buffer empty and `x22 ≥ 1` bytes left: compress all the blocks of
`data` but the last, `(x22 - 1) / B` of them, straight from `data`, leaving
`((x22 - 1) mod B) + 1` bytes. -/
def direct : Prog isa :=
  .seq (.block [.subImm .x .x9 .x22 1, .lsr .x .x10 .x9 (lbb w)])
    (.ite (.zero .x .x10) (.block [])
      (.seq (compressWith P [mov .x1 .x21, mov .x2 .x10, .addImm .x .x3 .x24 (B w), .movz .x .x4 0 0])
        (.block [.subImm .x .x9 .x22 1, .movz .x .x10 (BitVec.ofNat 16 (B w - 1)) 0,
          .logic .and .x .x9 .x9 .x10, .addImm .x .x9 .x9 1, .sub .x .x10 .x22 .x9,
          .add .x .x21 .x21 .x10, .add .x .x24 .x24 .x10, mov .x22 .x9])))

/-- Copy the last `x22` (1 to `B`) bytes of `data` to the (empty) buffer. -/
def tail : Prog isa :=
  .seq (.block [mov .x11 .x22, .add .x .x24 .x24 .x22, .movz .x .x22 0 0]) (copyLoop (w := w))

/-- The rest of `data`, if any, after `head`. -/
def rest : Prog isa :=
  .ite (.zero .x .x22) (.block []) (.seq (direct P) (tail (w := w)))

/-- Save registers and set up ours. -/
def updateStart : List Instr :=
  save .x4 ++ [mov .x19 .x0, mov .x20 .x4, mov .x21 .x2, mov .x22 .x3, mov .x24 .x1]

/-- `update`, but for saving `x30`. -/
def updateMain : Prog isa :=
  .seq (.block updateStart) (.seq (bufLen (w := w))
    (.seq (.ite (.zero .x .x22) (.block []) (.seq (head P) (rest P))) (.block restore)))

def update : Prog isa := .frame (.push .x30) (updateMain P) (.pop .x30)

/-! ## `finalize` -/

/-- The loop zeroing the buffer from byte `x23` on, `x11 ≥ 1` bytes (`x9 = 0`). -/
def zeroLoop : Prog isa :=
  .loop (.block [.add .x .x12 .x19 .x23, .strb .x9 .x12 (N w), .addImm .x .x23 .x23 1,
    .subImm .x .x11 .x11 1]) (.nonzero .x .x11)

/-- Zero the rest of the buffer. -/
def pad : Prog isa :=
  .seq (.block [.movz .x .x9 0 0, .movz .x .x11 (BitVec.ofNat 16 (B w)) 0, .sub .x .x11 .x11 .x23])
    (.ite (.zero .x .x11) (.block []) (zeroLoop (w := w)))

/-- Compress the buffer as the last block: its counter is the byte count. -/
def compressLast : Prog isa :=
  compressWith P [.addImm .x .x1 .x19 (N w), .movz .x .x2 1 0, mov .x3 .x24, .movz .x .x4 1 0]

/-- Copy the hash value (at `x19`) to `out` (at `x21`). -/
def output : List Instr :=
  (List.range (N w / 8)).flatMap fun k => [.ldr .x .x9 .x19 (8 * k), .str .x .x9 .x21 (8 * k)]

/-- `finalize`, but for saving `x30`. -/
def finalizeMain : Prog isa :=
  .seq (.block (save .x3 ++ [mov .x19 .x0, mov .x20 .x3, mov .x21 .x2, mov .x24 .x1]))
    (.seq (bufLen (w := w)) (.seq (pad (w := w)) (.seq (compressLast P)
      (.block (output (w := w) ++ restore)))))

def finalize : Prog isa := .frame (.push .x30) (finalizeMain P) (.pop .x30)

/-! ## `init`

Uses only `x0`–`x3` and `x9`–`x12`. -/

/-- `h := IV`, with the parameter block `0x0101kknn` XORed into `h[0]`
(`kk` = `keylen` in `x3`, `nn` = `outlen` in `x1`). -/
def initState : List Instr :=
  (List.finRange 7).flatMap (fun i =>
    movImm64 .x9 ((P.IV[i.1 + 1]'(by omega)).setWidth 64) ++ [.str (sz w) .x9 .x0 (ws w * (i.1 + 1))]) ++
  movImm64 .x9 ((P.IV[0] ^^^ 0x01010000).setWidth 64) ++
  [.lsl (sz w) .x10 .x3 8, .logic .eor (sz w) .x9 .x9 .x10, .logic .eor (sz w) .x9 .x9 .x1,
    .str (sz w) .x9 .x0 0]

/-- Zero the buffer and copy the `x3 ≥ 1` bytes of the key (at `x2`) to it. -/
def keyBlock : Prog isa :=
  .seq (.block (.movz .x .x9 0 0 :: ((List.range (B w / 8)).map fun j => .str .x .x9 .x0 (N w + 8 * j)) ++
      [.addImm .x .x12 .x0 (N w)]))
    (.loop (.block [.ldrb .x9 .x2 0, .strb .x9 .x12 0, .addImm .x .x2 .x2 1, .addImm .x .x12 .x12 1,
      .subImm .x .x3 .x3 1]) (.nonzero .x .x3))

def init : Prog isa :=
  .seq (.block (initState P)) (.ite (.zero .x .x3) (.block []) (keyBlock (w := w)))

end

end VG.Impl.Blake2.AArch64.Stream

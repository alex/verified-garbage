import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-!
# ML-DSA on AArch64: `vg_mldsa_hint_bit_pack` and `vg_mldsa_hint_bit_unpack`

Both follow Algorithms 20 and 21 (the spec's `hintBitPack` and
`hintBitUnpack`) step by step. They may leak the hint, and branch and index
memory on it; each first zeroes its output, whose contents are then a
function of the hint alone. Neither reads its 32-bit argument `omega`:
`ω = len - k` for `k = hlen / 256`, which the contracts require.

Comparisons of numbers less than `2⁶³` are the sign bit of their difference
(`sub`, then `lsr` by 63), and branches test it (`cbnz`).

* `hintBitPack(h = x0, hlen = x1, omega = w2, y = x3, len = x4)`: `k` into
  `x12` and `ω` into `x2`; zeroes the `len` bytes of `y`; then, with the
  index in `x5`, for each of the `k` polynomials (`x12` counting down; `x6`
  pointing at `y[ω + i]`) and each of their 256 coefficients (`x7` = `j`,
  `x8` counting down, `x0` walking the words), stores `j` to `y[index]` and
  increments the index if the coefficient is not 0, and then stores the
  index to `y[ω + i]`.
* `hintBitUnpack(y = x0, len = x1, omega = w2, h = x3, hlen = x4)`: `k` into
  `x12`, `ω` into `x2`, `y` into `x9`; zeroes the `hlen` words of `h`; then,
  with the index in `x5`, for each of the `k` polynomials (`x6` pointing at
  `y[ω + i]`, and `x3` at polynomial `i` of `h`), checks the bound
  `y[ω + i]` (in `x7`) against the index and `ω`, and sets the coefficients
  `y[index]` of the polynomial up to it (in `x10`), each after checking that
  it is at least one more than the previous one (`x11`, 0 before the first);
  then checks that the bytes from the index up to `ω` are zero. A failed
  check sets the index to 256 (more than `ω`, and than any byte), which ends
  the loop it is in and fails every later check; the return value is 1 if
  the index is at most `ω`, 0 otherwise.
-/

namespace VG.Impl.MlDsa.AArch64.Pack

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)

/-! ## `vg_mldsa_hint_bit_pack` -/

/-- `k`, `ω`, and the zeroing loop's pointer and count. -/
def hbpPro : List Instr :=
  [.lsr .x .x12 .x1 8, .sub .x .x2 .x4 .x12, .movz .x .x15 0 0, mov .x9 .x3, mov .x10 .x4]

/-- Zero the `len` bytes of `y`. -/
def hbpZero : Prog isa :=
  .loop (.block [.strb .x15 .x9 0, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1]) (.nonzero .x .x10)

def hbpInit : Prog isa := .seq (.block hbpPro) hbpZero

/-- `y[index] ← j`, and the index is incremented. -/
def hbpSet : List Instr := [.add .x .x10 .x3 .x5, .strb .x7 .x10 0, .addImm .x .x5 .x5 1]

/-- Coefficient `j = x7` of the polynomial, the word at `x0`: if it is not
0, `y[index] ← j` and the index is incremented. -/
def hbpCoef : Prog isa :=
  .seq (.block [.ldr .w .x9 .x0 0])
    (.seq (.ite (.nonzero .x .x9) (.block hbpSet) (.block []))
      (.block [.addImm .x .x0 .x0 4, .addImm .x .x7 .x7 1, .subImm .x .x8 .x8 1]))

/-- Polynomial `i`: its coefficients, then `y[ω + i] ← index`. -/
def hbpPoly : Prog isa :=
  .seq (.block [.movz .x .x7 0 0, .movz .x .x8 256 0])
    (.seq (.loop hbpCoef (.nonzero .x .x8))
      (.block [.strb .x5 .x6 0, .addImm .x .x6 .x6 1, .subImm .x .x12 .x12 1]))

/-- The `k` polynomials, from `x6 = y + ω`. -/
def hbpMain : Prog isa :=
  .seq (.block [.movz .x .x5 0 0, .add .x .x6 .x3 .x2]) (.loop hbpPoly (.nonzero .x .x12))

def hintBitPack : Prog isa := .seq hbpInit hbpMain

/-! ## `vg_mldsa_hint_bit_unpack` -/

/-- `k`, `ω`, `y`, and the zeroing loop's pointer and count. -/
def hbuPro : List Instr :=
  [.lsr .x .x12 .x4 8, .sub .x .x2 .x1 .x12, .movz .x .x15 0 0, mov .x9 .x0, mov .x10 .x3, mov .x8 .x4]

/-- Zero the `hlen` words of `h`. -/
def hbuZero : Prog isa :=
  .loop (.block [.str .w .x15 .x10 0, .addImm .x .x10 .x10 4, .subImm .x .x8 .x8 1]) (.nonzero .x .x8)

def hbuInit : Prog isa := .seq (.block hbuPro) hbuZero

/-- A failed check: the index becomes 256. -/
def hbuFail : Prog isa := .block [.movz .x .x5 256 0]

/-- Set coefficient `x10` of the polynomial at `x3` (`x15` is 1), increment
the index, and remember the coefficient plus one in `x11`. -/
def hbuSet : List Instr :=
  [.lsl .x .x14 .x10 2, .add .x .x14 .x3 .x14, .str .w .x15 .x14 0, .addImm .x .x5 .x5 1,
    .addImm .x .x11 .x10 1]

/-- The coefficient `y[index]` of the polynomial: at least `x11`, or fail;
then `x10` is 1 if the index is still less than the bound `x7`. -/
def hbuCoef : Prog isa :=
  .seq (.block [.add .x .x13 .x9 .x5, .ldrb .x10 .x13 0, .sub .x .x14 .x10 .x11, .lsr .x .x14 .x14 63])
    (.seq (.ite (.nonzero .x .x14) hbuFail (.block hbuSet))
      (.block [.sub .x .x10 .x5 .x7, .lsr .x .x10 .x10 63]))

/-- The coefficients of the polynomial, while the index is less than the
bound `x7`. -/
def hbuCoefs : Prog isa :=
  .seq (.block [.movz .x .x11 0 0, .sub .x .x10 .x5 .x7, .lsr .x .x10 .x10 63])
    (.ite (.nonzero .x .x10) (.loop hbuCoef (.nonzero .x .x10)) (.block []))

/-- Polynomial `i`: the bound `y[ω + i]`, which must be at least the index
and at most `ω`, and the coefficients up to it. -/
def hbuPoly : Prog isa :=
  .seq (.block [.ldrb .x7 .x6 0, .sub .x .x10 .x7 .x5, .sub .x .x11 .x2 .x7, .logic .orr .x .x10 .x10 .x11,
      .lsr .x .x10 .x10 63])
    (.ite (.nonzero .x .x10) hbuFail hbuCoefs)

/-- The `k` polynomials, from `x6 = y + ω`; `x15` is 1 from here on. -/
def hbuMain : Prog isa :=
  .seq (.block [.movz .x .x5 0 0, .movz .x .x15 1 0, .add .x .x6 .x9 .x2])
    (.loop (.seq hbuPoly (.block [.addImm .x .x6 .x6 1, .addImm .x .x3 .x3 1024, .subImm .x .x12 .x12 1]))
      (.nonzero .x .x12))

/-- A trailing byte `y[index]`: zero, or fail. -/
def hbuTrailByte : Prog isa :=
  .seq (.block [.add .x .x13 .x9 .x5, .ldrb .x10 .x13 0])
    (.seq (.ite (.nonzero .x .x10) hbuFail (.block [.addImm .x .x5 .x5 1]))
      (.block [.sub .x .x10 .x5 .x2, .lsr .x .x10 .x10 63]))

/-- The bytes from the index up to `ω` are zero, or fail. -/
def hbuTrail : Prog isa :=
  .seq (.block [.sub .x .x10 .x5 .x2, .lsr .x .x10 .x10 63])
    (.ite (.nonzero .x .x10) (.loop hbuTrailByte (.nonzero .x .x10)) (.block []))

/-- `x0 ← 1` if the index is at most `ω`, 0 otherwise. -/
def hbuRet : List Instr := [.sub .x .x10 .x2 .x5, .lsr .x .x10 .x10 63, .logic .eor .x .x0 .x10 .x15]

def hintBitUnpack : Prog isa := .seq hbuInit (.seq hbuMain (.seq hbuTrail (.block hbuRet)))

end VG.Impl.MlDsa.AArch64.Pack

import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Stream

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_pack` and `vg_mldsa_hint_bit_unpack`

Both follow Algorithms 20 and 21 (the spec's `hintBitPack` and
`hintBitUnpack`) step by step, as on x86-64. They may leak the hint, and
branch and index memory on it; each first zeroes its output, whose contents
are then a function of the hint alone. The model branches only on `Z`: a
comparison `x < y` of small numbers is the sign bit of `x - y`
(`ltBit`), compared with zero. Each saves the registers it needs beyond
`r0`–`r3` and `r12` in a frame on the stack, and reloads all but the first
from it at the end (the pop reloads the first).

* `hintBitPack(h = r0, hlen = r1, omega = r2, y = r3, len = [sp])`: zeroes
  the `len` bytes of `y`; then, with the index in `r1`, for each of the `k`
  polynomials (`r4` counting down; `r5` pointing at `y[ω + i]`) and each of
  their 256 coefficients (`r12` = `j`, `r0` walking the words), stores `j`
  to `y[index]` and increments the index if the coefficient is not 0, and
  then stores the index to `y[ω + i]`.
* `hintBitUnpack(y = r0, len = r1, omega = r2, h = r3, hlen = [sp])`:
  zeroes the `hlen` words of `h`; then, with the index in `r1`, for each of
  the `k` polynomials (`r6` counting down; `r5` pointing at `y[ω + i]`, and
  `r3` at polynomial `i` of `h`), unless a check failed (the index is at
  most `ω`), checks the bound `y[ω + i]` (in `r4`) against the index and
  `ω`, and sets the coefficients `y[index]` of the polynomial up to it, each
  but the first after checking that it is greater than the previous one;
  then checks that the bytes from the index up to `ω` are zero. A failed
  check sets the index to 256 (more than `ω`, and than any byte), which ends
  the loop it is in and skips the rest; the return value is 1 if the index
  is at most `ω`, 0 otherwise.
-/

namespace VG.Impl.MlDsa.Arm.Pack

open VG.Arm

/-- `t ← 1` if `x < y`, `0` otherwise, for `x` and `y` less than `2³¹`: the
sign bit of `x - y`; then `Z` is set iff `x ≥ y`. -/
def ltBit (t x y : Reg) : List Instr := [.dp .sub t x (.reg y), .mov t (.shifted t .lsr 31), .cmp t (.imm 0)]

/-! ## `vg_mldsa_hint_bit_pack` -/

/-- Zero the `len` bytes of `y` (`r3`), with `r5` walking them and `r4`
counting; `r12` is then 0. -/
def hbpZero : Prog isa :=
  .seq (.block [.ldrSp .r4 8, .mov .r12 (.imm 0), .mov .r5 (.reg .r3)])
    (.loop (.block [.strb .r12 .r5 0, .dp .add .r5 .r5 (.imm 1), .subs .r4 .r4 (.imm 1)]) .ne)

/-- Coefficient `j = r12` of the polynomial, the word at `r0`: if it is not
0, `y[index] ← j` and the index is incremented. -/
def hbpCoef : Prog isa :=
  .seq (.block [.ldr .r2 .r0 0, .cmp .r2 (.imm 0)])
    (.seq (.ite .eq (.block []) (.block [.dp .add .r2 .r3 (.reg .r1), .strb .r12 .r2 0, .dp .add .r1 .r1 (.imm 1)]))
      (.block [.dp .add .r0 .r0 (.imm 4), .dp .add .r12 .r12 (.imm 1), .cmp .r12 (.imm 256)]))

/-- Polynomial `i`: its coefficients, then `y[ω + i] ← index`. -/
def hbpPoly : Prog isa :=
  .seq (.block [.mov .r12 (.imm 0)])
    (.seq (.loop hbpCoef .ne) (.block [.strb .r1 .r5 0, .dp .add .r5 .r5 (.imm 1), .subs .r4 .r4 (.imm 1)]))

/-- The `k = len - ω` polynomials, from `r5 = y + ω`, the index `r1` from 0. -/
def hbpMain : Prog isa :=
  .seq (.block [.ldrSp .r4 8, .dp .sub .r4 .r4 (.reg .r2), .dp .add .r5 .r3 (.reg .r2), .mov .r1 (.imm 0)])
    (.loop hbpPoly .ne)

/-- The body of `hintBitPack`, in its frame (`r4`, `r5`; `len` at `[sp, #8]`). -/
def hintBitPackBody : Prog isa := .seq hbpZero (.seq hbpMain (.block [.ldrSp .r5 4]))

def hintBitPack : Prog isa := .frame (.push [.r4, .r5]) hintBitPackBody (.pop .r4 8)

/-! ## `vg_mldsa_hint_bit_unpack` -/

/-- `k = len - ω` into `r6`; zero the `hlen` words of `h` (`r3`), with `r5`
walking them and `r4` counting; the index `r1` then 0. -/
def hbuZero : Prog isa :=
  .seq (.block [.dp .sub .r6 .r1 (.reg .r2), .ldrSp .r4 16, .mov .r12 (.imm 0), .mov .r5 (.reg .r3)])
    (.seq (.loop (.block [.str .r12 .r5 0, .dp .add .r5 .r5 (.imm 4), .subs .r4 .r4 (.imm 1)]) .ne)
      (.block [.mov .r1 (.imm 0)]))

/-- A failed check: the index becomes 256. -/
def hbuFail : Prog isa := .block [.mov .r1 (.imm 256)]

/-- Set coefficient `y[index]` of the polynomial at `r3`, and increment the
index. -/
def hbuSet : List Instr :=
  [.dp .add .r12 .r0 (.reg .r1), .ldrb .r12 .r12 0, .dp .add .r12 .r3 (.shifted .r12 .lsl 2), .mov .r7 (.imm 1),
    .str .r7 .r12 0, .dp .add .r1 .r1 (.imm 1)]

/-- `Z` clear iff the index is less than the bound `r4` (in `r7`). -/
def hbuMore : List Instr := ltBit .r7 .r1 .r4

/-- A coefficient after the first: `y[index - 1] < y[index]`, or fail. -/
def hbuNext : Prog isa :=
  .seq (.block ([.dp .add .r12 .r0 (.reg .r1), .ldrb .r7 .r12 0, .dp .sub .r12 .r12 (.imm 1), .ldrb .r12 .r12 0] ++
      ltBit .r7 .r12 .r7))
    (.seq (.ite .eq hbuFail (.block hbuSet)) (.block hbuMore))

/-- The coefficients of the polynomial, while the index is less than the
bound `r4`: the first, then the others. -/
def hbuCoefs : Prog isa :=
  .seq (.block hbuMore)
    (.ite .eq (.block [])
      (.seq (.block (hbuSet ++ hbuMore)) (.ite .eq (.block []) (.loop hbuNext .ne))))

/-- Polynomial `i`, unless a check failed: the bound `y[ω + i]`, checked
against the index and `ω`, and the coefficients up to it. -/
def hbuPoly : Prog isa :=
  .seq (.block (ltBit .r7 .r2 .r1))
    (.ite .eq
      (.seq (.block ([.ldrb .r4 .r5 0] ++ ltBit .r7 .r4 .r1))
        (.ite .eq (.seq (.block (ltBit .r7 .r2 .r4)) (.ite .eq hbuCoefs hbuFail)) hbuFail))
      (.block []))

/-- The `k` polynomials, from `r5 = y + ω`. -/
def hbuMain : Prog isa :=
  .seq (.block [.dp .add .r5 .r0 (.reg .r2)])
    (.loop (.seq hbuPoly (.block [.dp .add .r5 .r5 (.imm 1), .dp .add .r3 .r3 (.imm 1024), .subs .r6 .r6 (.imm 1)]))
      .ne)

/-- The bytes from the index up to `ω` are zero, or fail. -/
def hbuTrail : Prog isa :=
  .seq (.block (ltBit .r7 .r1 .r2))
    (.ite .eq (.block [])
      (.loop (.seq (.block [.dp .add .r12 .r0 (.reg .r1), .ldrb .r12 .r12 0, .cmp .r12 (.imm 0)])
        (.seq (.ite .eq (.block [.dp .add .r1 .r1 (.imm 1)]) hbuFail) (.block (ltBit .r7 .r1 .r2)))) .ne))

/-- `r0 ← 1` if the index is at most `ω`, 0 otherwise; then the saved
registers reloaded (the pop reloads `r4`). -/
def hbuRet : List Instr :=
  [.dp .sub .r7 .r2 (.reg .r1), .mov .r7 (.shifted .r7 .lsr 31), .mov .r0 (.imm 1), .dp .sub .r0 .r0 (.reg .r7),
    .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12]

/-- The body of `hintBitUnpack`, in its frame (`r4`–`r7`; `hlen` at
`[sp, #16]`). -/
def hintBitUnpackBody : Prog isa := .seq hbuZero (.seq hbuMain (.seq hbuTrail (.block hbuRet)))

def hintBitUnpack : Prog isa := .frame (.push [.r4, .r5, .r6, .r7]) hintBitUnpackBody (.pop .r4 16)

end VG.Impl.MlDsa.Arm.Pack

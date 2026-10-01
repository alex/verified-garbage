import VerifiedGarbage.Impl.Ed25519.CombTable
import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Impl.Ed25519.AArch64.PointLoop

/-!
# Ed25519: base-point multiplication with a comb, two digits per table

The scalar's 64 nibbles `n_i` (from its bits, expanded one per byte at byte
768 of the workspace) give `[s]B = Σ d_i [16^i]B + [17 G]B` for the digits
`d_i = n_i - 8`, from `-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`. Table `j`
holds `[k]([256^j]B)` for `k ≤ 8` (`combCached`), affine. Step `j` selects
from table `j` the entries of both digits that use it, `d_{2j+1}` and
`d_{2j}`, sharing each candidate's immediates between the two selections,
and adds them, or their negations, to two accumulators, which start at
`[G]B`: `A` (slots 0–3) for the odd digits and `B` (slots 17–20) for the even
ones. At the end, `[s]B = 16 A + B`: four doublings and one addition. That
is 64 additions of affine cached points (seven multiplications each,
`addOddOps`, `addEvenOps`), four doublings and one addition.

The digits are secret: their entries are selected in constant time. The
masks of the eight magnitudes `k = 1 … 8` (all ones exactly for `|d|`) and
the bit of `|d| = 0` of both digits stay in registers (`oddRegs`, `x22`;
`evenRegs`, `x8`). Each candidate word is built from immediates once, masked
with both digits' masks and ORed into `x4` (odd) and `x5` (even). Each entry
is negated, or not, with the mask of its digit's sign (from its nibble's top bit), by
exchanging `Y - X` and `Y + X` and choosing between `2dT` and its negation.
The loop's counter `x19`, which is also the table index, is public.
-/

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

/-- Add the affine cached point in slots 4–6 (`[Y - X, Y + X, 2dT]` of a point with `Z = 1`,
so its `2Z` is `2` and `Z₁ · 2Z₂` is `Z₁ + Z₁`) to the odd digits' accumulator in slots 0–3,
in place: `a = (Y₁ - X₁)(Y₂ - X₂)`, `b = (Y₁ + X₁)(Y₂ + X₂)`, `c = T₁ · 2dT₂`, `dd = 2Z₁`,
`h = b + a`, `e = b - a`, `g = dd + c`, `f = dd - c`, and `(ef, gh, fg, eh)`. Slots 8–12 are
temporary. -/
def addOddOps : List FieldOp := [
  .sub 8 1 0, .mul 8 8 4, .add 9 1 0, .mul 9 9 5, .mul 10 3 6, .add 11 2 2,
  .add 12 9 8, .sub 8 9 8, .add 9 11 10, .sub 10 11 10,
  .mul 0 8 10, .mul 1 9 12, .mul 2 10 9, .mul 3 8 12]

/-- The same addition, of the even digits' entry in slots 13–15 to their accumulator in
slots 17–20. -/
def addEvenOps : List FieldOp := [
  .sub 8 18 17, .mul 8 8 13, .add 9 18 17, .mul 9 9 14, .mul 10 20 15, .add 11 19 19,
  .add 12 9 8, .sub 8 9 8, .add 9 11 10, .sub 10 11 10,
  .mul 17 8 10, .mul 18 9 12, .mul 19 10 9, .mul 20 8 12]

/-- Four doublings, with the counter `x1`. -/
def double4 : Prog isa :=
  .seq (.block [.movz .w .x1 4 0]) (.loop (.block doubleBody) (.nonzero .x .x1))

/-- `x2` = the nibble `b₀ + 2b₁ + 4b₂ + 8b₃` of the bits at `x8 + o`, by Horner's rule. -/
def combNibble (o : Nat) : List Instr :=
  [.ldrb .x2 .x8 (o + 3), .add .x .x2 .x2 .x2, .ldrb .x3 .x8 (o + 2), .add .x .x2 .x2 .x3,
    .add .x .x2 .x2 .x2, .ldrb .x3 .x8 (o + 1), .add .x .x2 .x2 .x3,
    .add .x .x2 .x2 .x2, .ldrb .x3 .x8 o, .add .x .x2 .x2 .x3]

/-- From the nibble `n` in `x2`: the sign's mask (all ones if `n < 8`) into `x1`, and
`|n - 8|` into `x2`. -/
def combSign : List Instr :=
  [.subImm .x .x3 .x2 8, .lsr .x .x1 .x3 63, .movz .w .x9 0 0, .sub .x .x1 .x9 .x1,
    .logic .eor .x .x2 .x3 .x1, .sub .x .x2 .x2 .x1]

/-- The registers holding the masks of the odd digit's magnitudes `1 … 8`. -/
def oddRegs : List Reg := [.x12, .x13, .x14, .x15, .x16, .x17, .x20, .x21]

/-- The registers holding the masks of the even digit's magnitudes `1 … 8`. -/
def evenRegs : List Reg := [.x1, .x3, .x6, .x7, .x10, .x11, .x23, .x24]

/-- Mask `k` of the odd digit. -/
def oddReg (k : Nat) : Reg := oddRegs.getD (k - 1) .x12

/-- Mask `k` of the even digit. -/
def evenReg (k : Nat) : Reg := evenRegs.getD (k - 1) .x1

/-- `z` = `[|d| < 1]` and `rs[k - 1]` = `[|d| < k]` for `k = 1 … 8`, then
`rs[k - 1]` = `[|d| < k] - [|d| < k + 1]`: all ones exactly if `|d| = k`, for `|d|` in `x2`. -/
def combMasks (rs : List Reg) (z : Reg) : List Instr :=
  [.subImm .x z .x2 1, .lsr .x z z 63] ++
    (List.range 8).flatMap (fun k =>
      [.subImm .x (rs.getD k .x1) .x2 (k + 1), .lsr .x (rs.getD k .x1) (rs.getD k .x1) 63]) ++
    (List.range 8).map fun k =>
      if k < 7 then .sub .x (rs.getD k .x1) (rs.getD k .x1) (rs.getD (k + 1) .x1)
      else .subImm .x (rs.getD k .x1) (rs.getD k .x1) 1

/-- The odd digit `d_{2j+1}` (bits at `x8 + 772`): its masks to `oddRegs` and `x22`; then the
even digit `d_{2j}` (bits at `x8 + 768`): its masks to `evenRegs` and `x8`. -/
def combDigits : List Instr :=
  [.lsl .x .x8 .x19 3, .add .x .x8 .x0 .x8] ++
    combNibble 772 ++ combSign ++ combMasks oddRegs .x22 ++
    combNibble 768 ++ combSign ++ combMasks evenRegs .x8

/-- Word `w` of a field element. -/
def feWord (v : Spec.X25519.Fe) (w : Nat) : BitVec 64 := BitVec.ofNat 64 (v.val / 2 ^ (64 * w))

/-- Word `w` of candidate `k`'s value `v`, built once, masked with each digit's mask and ORed
into `x4` (odd) and `x5` (even). -/
def selectCand (v : Spec.X25519.Fe) (k w : Nat) : List Instr :=
  const64 .x9 (feWord v w) ++
    [.logic .and .x .x2 .x9 (oddReg k), .logic .orr .x .x4 .x4 .x2,
      .logic .and .x .x2 .x9 (evenReg k), .logic .orr .x .x5 .x5 .x2]

/-- The start of word `w`'s selections: `1` for `|d| = 0` in word 0 of the identity's
`Y - X` and `Y + X` (`one`), else `0`. -/
def selectStart (one : Bool) (w : Nat) : List Instr :=
  if one && w == 0 then [.addImm .x .x4 .x22 0, .addImm .x .x5 .x8 0]
  else [.movz .w .x4 0 0, .movz .w .x5 0 0]

/-- Word `w` of `vs[|d|]` for both digits, to bytes `o + 8w` (odd) and `e + 8w` (even), where
`vs[0]` is `1` (if `one`) or `0`. -/
def selectWord (one : Bool) (vs : List Spec.X25519.Fe) (o e w : Nat) : List Instr :=
  selectStart one w ++ (List.range 8).flatMap (fun k => selectCand (vs.getD (k + 1) 0) (k + 1) w) ++
    [st .x4 (o + 8 * w), st .x5 (e + 8 * w)]

/-- The field `vs[|d|]` for both digits, to bytes `o` (odd) and `e` (even). -/
def selectField (one : Bool) (vs : List Spec.X25519.Fe) (o e : Nat) : List Instr :=
  (List.range 4).flatMap fun w => selectWord one vs o e w

/-- The entries of both digits from table `j`: the odd one to slots 4–6, the even one to
slots 13–15. -/
def combSelect (j : Nat) : List Instr :=
  let entries := (List.range 9).map (combCached j)
  selectField true (entries.map (·.X)) (offset 4) (offset 13) ++
    selectField true (entries.map (·.Y)) (offset 5) (offset 14) ++
    selectField false (entries.map (·.Z)) (offset 6) (offset 15)

/-- The selection from table `x19`, for the table indices listed. -/
def combSelectFrom : List Nat → Prog isa
  | [] => .block []
  | j :: js => .seq (.block [.subImm .x .x9 .x19 j])
      (.ite (.zero .x .x9) (.block (combSelect j)) (combSelectFrom js))

/-- The cached point in slots `a`, `b`, `c` negated if its digit is negative, that is if the
top bit of its nibble (at `x0 + 8 x19 + o + 3`) is clear, its mask `bit - 1` all ones:
`[Y - X, Y + X, 2dT]` becomes `[Y + X, Y - X, -2dT]`, by exchanging slots `a` and `b`, and
slots `c` and 8 (`0 - 2dT`, with zero in slot 21). -/
def combNeg (a b c : Slot) (o : Nat) : List Instr :=
  fieldCode [.sub 8 21 c] ++
    [.lsl .x .x3 .x19 3, .add .x .x3 .x0 .x3, .ldrb .x3 .x3 (o + 3), .subImm .x .x3 .x3 1] ++
    swapFields [(a, b), (c, 8)]

/-- Step `x19 = j`: both digits' entries of table `j`, negated for negative digits, added to
their accumulators. `x8` is nonzero while another step follows. -/
def combStep : Prog isa :=
  .seq (.block combDigits) <|
  .seq (combSelectFrom (List.range 32)) <|
  .block (combNeg 4 5 6 772 ++ fieldCode addOddOps ++
    combNeg 13 14 15 768 ++ fieldCode addEvenOps ++
    [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 32])

/-- Both accumulators at `[G]B`, zero in slot 21, and the counter. -/
def combInit : List Instr :=
  fieldCode ([.const 21 0] ++ constPointOps combG ++
    [.const 17 combG.X, .const 18 combG.Y, .const 19 combG.Z, .const 20 combG.T]) ++
    [.movz .w .x19 0 0]

/-- `16 A + B` into slots 0–3. -/
def combFinish : Prog isa :=
  .seq (.block (fieldCode [.const 16 Spec.Ed25519.d])) <|
  .seq double4 (.block (fieldCode [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] ++ pointAdd))

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768 onward. -/
def combMultiply : Prog isa :=
  .seq (.block combInit) (.seq (.loop combStep (.nonzero .x .x8)) combFinish)

end VG.Impl.Ed25519.AArch64

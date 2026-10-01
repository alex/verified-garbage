import VerifiedGarbage.Impl.Ed25519.CombTable
import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Impl.Ed25519.AArch64.PointLoop

/-!
# Ed25519: base-point multiplication with a comb

The scalar's 64 nibbles `n_i` (from its bits, expanded one per byte at byte
768 of the workspace) give `[s]B = Σ d_i [16^i]B + [16 G + G]B` for the
digits `d_i = n_i - 8`, from `-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`.
Table `j` holds `[k]([256^j]B)` for `k ≤ 8` (`combCached`), affine, so from
`[G]B` the odd digits `d_{2j+1}` are added first, one from each table, as
the entry `|d|` or its negation; four doublings multiply their sum by 16,
and `[G]B` is added again; then the even digits `d_{2j}` are added from the
same tables. That is 65 additions of affine cached points (seven
multiplications each, `pointAddMixed`) and four doublings.

The digit is secret: its entry is selected in constant time. The masks of
the eight magnitudes `k = 1 … 8` (all ones exactly for `|d|`) and the bit of
`|d| = 0` stay in registers (`combMaskRegs`, `x22`); every candidate's words
are built from immediates, masked and ORed into `x4`–`x7`. The entry is
negated, or not, with the mask of the digit's sign (`x1`), by exchanging
`Y - X` and `Y + X` and choosing between `2dT` and its negation. The loop's
counter `x19` and the table index are public.
-/

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

/-- Add the affine cached point in slots 4–6 (`[Y - X, Y + X, 2dT]` of `q`, with `Z = 1`) to
the point in slots 0–3, in place. Slots 8–15 are temporary. -/
def pointAddMixedOps : List FieldOp := [
  .sub 8 1 0, .mul 8 8 4,
  .add 9 1 0, .mul 9 9 5,
  .mul 10 3 6, .add 11 2 2,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

def pointAddMixed : List Instr := fieldCode pointAddMixedOps

/-- Four doublings, with the counter `x1`. -/
def double4 : Prog isa :=
  .seq (.block [.movz .w .x1 4 0]) (.loop (.block doubleBody) (.nonzero .x .x1))

/-- `[G]B` added to slots 0–3. -/
def combAddG : List Instr :=
  fieldCode [.const 4 combGCached.X, .const 5 combGCached.Y, .const 6 combGCached.Z] ++ pointAddMixed

/-- `x8` = the workspace address plus the bit index `4 combIdx c` of step `c = x19`'s digit:
`8c + 4` for an odd digit (`c < 32`), `8c - 256` for an even one. -/
def combIndex : Prog isa :=
  .seq (.block [.lsr .x .x8 .x19 5, .lsl .x .x2 .x19 3])
    (.seq (.ite (.zero .x .x8) (.block [.addImm .x .x2 .x2 4]) (.block [.subImm .x .x2 .x2 256]))
      (.block [.add .x .x8 .x0 .x2]))

/-- `x2` = the nibble `b₀ + 2b₁ + 4b₂ + 8b₃` of the bits at `x8 + 768`, by Horner's rule. -/
def combNibble : List Instr :=
  [.ldrb .x2 .x8 771, .add .x .x2 .x2 .x2, .ldrb .x3 .x8 770, .add .x .x2 .x2 .x3,
    .add .x .x2 .x2 .x2, .ldrb .x3 .x8 769, .add .x .x2 .x2 .x3,
    .add .x .x2 .x2 .x2, .ldrb .x3 .x8 768, .add .x .x2 .x2 .x3]

/-- From the nibble `n` in `x2`: the sign's mask (all ones if `n < 8`) into `x1`, and
`|n - 8|` into `x2`. -/
def combSign : List Instr :=
  [.subImm .x .x3 .x2 8, .lsr .x .x1 .x3 63, .movz .w .x9 0 0, .sub .x .x1 .x9 .x1,
    .logic .eor .x .x2 .x3 .x1, .sub .x .x2 .x2 .x1]

/-- The registers holding the masks of the magnitudes `1 … 8`. -/
def combMaskRegs : List Reg := [.x12, .x13, .x14, .x15, .x16, .x17, .x20, .x21]

def maskReg (k : Nat) : Reg := combMaskRegs.getD (k - 1) .x12

/-- `x22` = `[|d| < 1]`; `maskReg k` = `[|d| < k]` for `k = 1 … 8`. -/
def combLess (k : Nat) : List Instr := [.subImm .x .x9 .x2 k, .lsr .x (maskReg k) .x9 63]

/-- `maskReg k` = `[|d| < k] - [|d| < k + 1]`: all ones exactly if `|d| = k`. -/
def combDiff (k : Nat) : Instr :=
  if k < 8 then .sub .x (maskReg k) (maskReg k) (maskReg (k + 1)) else .subImm .x (maskReg 8) (maskReg 8) 1

/-- The masks of `|d|` in `x2`. -/
def combMasks : List Instr :=
  [.subImm .x .x9 .x2 1, .lsr .x .x22 .x9 63] ++ (List.range 8).flatMap (fun k => combLess (k + 1)) ++
    (List.range 8).map fun k => combDiff (k + 1)

/-- Word `w` of a field element. -/
def feWord (v : Spec.X25519.Fe) (w : Nat) : BitVec 64 := BitVec.ofNat 64 (v.val / 2 ^ (64 * w))

/-- Word `w` of candidate `k`'s value `v`, masked, ORed into `x4`–`x7`. -/
def selectWord (v : Spec.X25519.Fe) (k w : Nat) : List Instr :=
  const64 .x9 (feWord v w) ++ [.logic .and .x .x9 .x9 (maskReg k), .logic .orr .x (wordReg w) (wordReg w) .x9]

/-- Candidate `k`'s value `v`, masked, ORed into `x4`–`x7`. -/
def selectCand (v : Spec.X25519.Fe) (k : Nat) : List Instr :=
  (List.range 4).flatMap fun w => selectWord v k w

/-- The start of a selection: `1` for `|d| = 0` (the identity's `Y - X` and `Y + X`). -/
def selectOne : List Instr := [.addImm .x .x4 .x22 0, .movz .w .x5 0 0, .movz .w .x6 0 0, .movz .w .x7 0 0]

/-- The field element `vs[|d|]` to byte `dst`, where `vs[0]` is `1` (if `one`) or `0`. -/
def selectField (one : Bool) (vs : List Spec.X25519.Fe) (dst : Nat) : List Instr :=
  (if one then selectOne else zero4) ++
    (List.range 8).flatMap (fun k => selectCand (vs.getD (k + 1) 0) (k + 1)) ++ store4 dst

/-- Entry `|d|` of table `j` to slots 4–6. -/
def combSelect (j : Nat) : List Instr :=
  let entries := (List.range 9).map (combCached j)
  selectField true (entries.map (·.X)) (offset 4) ++ selectField true (entries.map (·.Y)) (offset 5) ++
    selectField false (entries.map (·.Z)) (offset 6)

/-- The selection from table `x8`, for the table indices listed. -/
def combSelectFrom : List Nat → Prog isa
  | [] => .block []
  | j :: js => .seq (.block [.subImm .x .x9 .x8 j])
      (.ite (.zero .x .x9) (.block (combSelect j)) (combSelectFrom js))

/-- The cached point in slots 4–6 negated if the sign's mask `x1` is all ones:
`[Y - X, Y + X, 2dT]` becomes `[Y + X, Y - X, -2dT]`, by exchanging slots 4 and 5, and
slots 6 and 8 (`0 - 2dT`, with zero in slot 21). -/
def combNeg : List Instr :=
  fieldCode [.sub 8 21 6] ++ [mov .x3 .x1] ++ swapFields [(4, 5), (6, 8)]

/-- Step `x19 = c`: before the even digits, the four doublings and `[G]B`; then the digit's
entry of table `c mod 32`, negated for a negative digit, added. `x8` is nonzero while
another step follows. -/
def combStep : Prog isa :=
  .seq (.block [.subImm .x .x8 .x19 32]) <|
  .seq (.ite (.zero .x .x8) (.seq double4 (.block combAddG)) (.block [])) <|
  .seq combIndex <|
  .seq (.block (combNibble ++ combSign ++ combMasks ++ [.lsl .x .x8 .x19 59, .lsr .x .x8 .x8 59])) <|
  .seq (combSelectFrom (List.range 32)) <|
  .block (combNeg ++ pointAddMixed ++ [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 64])

def combInit : List Instr :=
  fieldCode [.const 16 Spec.Ed25519.d, .const 21 0] ++ constPoint combG ++ [.movz .w .x19 0 0]

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768 onward. -/
def combMultiply : Prog isa := .seq (.block combInit) (.loop combStep (.nonzero .x .x8))

end VG.Impl.Ed25519.AArch64

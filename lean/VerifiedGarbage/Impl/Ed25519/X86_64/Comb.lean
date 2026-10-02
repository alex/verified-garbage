import VerifiedGarbage.Impl.Ed25519.X86_64.CombTable
import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyWindow
import VerifiedGarbage.Impl.Ed25519.X86_64.PointSelect

/-!
# Ed25519: base-point multiplication with a comb

The scalar's 64 nibbles `n_i` (4-bit digits, from the bits at byte 768 of the
scratch) give `[s]B = Σ n_i [16^i]B = Σ d_i [16^i]B + [16 G + G]B` for the
digits `d_i = n_i - 8`, from `-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`.
Table `j` holds `[k]([256^j]B)` for `k ≤ 8`, so, from `[G]B`, the odd digits
`d_{2j+1}` are added first, one from each table, as the entry `|d|` or its
negation; four doublings multiply their sum by 16, and `[G]B` is added again;
then the even digits `d_{2j}` are added from the same tables. That is 65
additions of cached points and four doublings.

The digit is secret: each table entry is selected in constant time, every
candidate's words masked by a word that is all ones exactly for the digit's
magnitude (`combMask`, at byte 1024), and the entry negated, or not, with
the mask of the digit's sign (at byte 1152) by exchanging `Y - X` and `Y + X`
and choosing between `2dT` and its negation. The loop's counter `rbx` and the
table index `rdx` are public.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (sc zero4 store4)

/-- Byte of the scratch holding the nine candidates' masks. -/
def combMasks : Nat := 1024

/-- Byte of the scratch holding the mask of the digit's sign. -/
def combSignMask : Nat := 1152

/-- A bit of the expanded scalar, at bit index `rcx + i`. -/
def combBit (dst : Reg) (i : Nat) : Instr :=
  .movzx8 dst { base := .rdi, index := some .rcx, disp := 768 + i }

/-- `rax` = the digit `b₀ + 2b₁ + 4b₂ + 8b₃` of the bits at index `rcx`, by Horner's rule. -/
def combDigit : List Instr :=
  [combBit .rax 3, .alu .add .rax (.reg .rax), combBit .rdx 2, .alu .add .rax (.reg .rdx),
    .alu .add .rax (.reg .rax), combBit .rdx 1, .alu .add .rax (.reg .rdx),
    .alu .add .rax (.reg .rax), combBit .rdx 0, .alu .add .rax (.reg .rdx)]

/-- The mask of candidate `k`: all ones if `rax = k`, else zero (`rax ⊕ k - 1` borrows
exactly when `rax = k`). -/
def combMask (k : Nat) : List Instr :=
  [.mov .rdx (.reg .rax), .alu .xor .rdx (.imm (BitVec.ofNat 32 k)), .alu .sub .rdx (.imm 1),
    .alu .sbb .rdx (.reg .rdx), .store (sc (combMasks + 8 * k)) .rdx]

def combMaskAll : List Instr := (List.range 9).flatMap combMask

/-- From the nibble `n` in `rax`: the sign's mask (all ones if `n < 8`, from the borrow of
`n - 8`) to byte `combSignMask`, and `|n - 8|` into `rax`. -/
def combSign : List Instr :=
  [.alu .sub .rax (.imm 8), .alu .sbb .rdx (.reg .rdx), .store (sc combSignMask) .rdx,
    .alu .xor .rax (.reg .rdx), .alu .sub .rax (.reg .rdx)]

/-- Word `w` of a field element. -/
def feWord (v : Spec.X25519.Fe) (w : Nat) : BitVec 64 := BitVec.ofNat 64 (v.val / 2 ^ (64 * w))

/-- The register accumulating word `w`. -/
def wordReg (w : Nat) : Reg := [Reg.r8, .r9, .r10, .r11].getD w .r8

/-- Word `w` of candidate `k`'s value `v`, masked, into its register. -/
def selectWord (v : Spec.X25519.Fe) (k w : Nat) : List Instr :=
  [.movImm64 .rcx (feWord v w), .alu .and .rcx (.mem (sc (combMasks + 8 * k))),
    .alu .or (wordReg w) (.reg .rcx)]

/-- The field element `vs[k]` for the digit `k` to byte `dst`. -/
def selectField (vs : List Spec.X25519.Fe) (dst : Nat) : List Instr :=
  zero4 ++ (List.range 9).flatMap (fun k => (List.range 4).flatMap fun w =>
    selectWord (vs.getD k 0) k w) ++ store4 dst

/-- Entry `rax` of table `j` to slots 4–7. -/
def combSelect (j : Nat) : List Instr :=
  let entries := (List.range 9).map (combCached j)
  selectField (entries.map (·.X)) (offset 4) ++ selectField (entries.map (·.Y)) (offset 5) ++
    selectField (entries.map (·.Z)) (offset 6) ++ selectField (entries.map (·.T)) (offset 7)

/-- The cached point in slots 4–7 negated if the sign's mask is all ones:
`[Y - X, Y + X, 2dT, 2Z]` becomes `[Y + X, Y - X, -2dT, 2Z]`, by exchanging slots 4
and 5, and slots 6 and 8 (`-2dT`), under the mask in `rcx`. -/
def combNeg (fld : Arith) : List Instr :=
  fieldCode fld [.const 9 0, .sub 8 9 6] ++ [.mov .rcx (.mem (sc combSignMask))] ++
    swapFields [(4, 5), (6, 8)]

/-- The selection from table `rdx`, for the table indices listed. -/
def combSelectFrom : List Nat → Prog isa
  | [] => .block []
  | j :: js => .seq (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 j))])
      (.ite .e (.block (combSelect j)) (combSelectFrom js))

/-- `rcx` = the bit index of digit `2 rbx + 1` (odd digits, `rbx < 32`) or `2 (rbx - 32)`. -/
def combIndex : Prog isa :=
  .seq (.block [.mov .rcx (.reg .rbx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .cmp .rbx (.imm 32)])
    (.ite .b (.block [.alu .add .rcx (.imm 4)]) (.block [.alu .sub .rcx (.imm 256)]))

/-- `[G]B` added to slots 0–3. -/
def combAddG (fld : Arith) : List Instr :=
  fieldCode fld [.const 4 combGCached.X, .const 5 combGCached.Y, .const 6 combGCached.Z,
    .const 7 combGCached.T] ++ pointAddCached fld

/-- Step `rbx`: before the even digits, the four doublings and `[G]B`; then the digit's entry
of table `rbx mod 32`, negated for a negative digit, added. -/
def combStep (fld : Arith) : Prog isa :=
  .seq (.block [.alu .cmp .rbx (.imm 32)]) <|
  .seq (.ite .e (.seq (double4 fld) (.block (combAddG fld))) (.block [])) <|
  .seq combIndex <|
  .seq (.block (combDigit ++ combSign ++ combMaskAll ++ [.mov .rdx (.reg .rbx), .alu .and .rdx (.imm 31)])) <|
  .seq (combSelectFrom (List.range 32)) <|
  .block (combNeg fld ++ pointAddCached fld ++ [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 64)])

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768 onward. -/
def combMultiply (fld : Arith) : Prog isa :=
  .seq (.block (constPoint fld combG ++ [.mov32 .rbx (.imm 0)]))
    (.loop (combStep fld) .ne)

end VG.Impl.Ed25519.X86_64

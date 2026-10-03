import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
import VerifiedGarbage.Proof.Ed448.X86_64.BaseField

/-!
# Ed448 verification's equation on x86-64: field programs

The field programs of `vg_ed448_verify_equation` (`Impl/Ed448/X86_64/
VerifyEquation.lean`) evaluated on the slots: the doubling and the addition
at the slots they are used with (RFC 8032 §5.2.4's formulas, as for
base-point multiplication), and the steps of decoding.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Index Env)

theorem doubleAt_valid0 : ∀ op ∈ doubleAt 0 1 2, fopValid op := by decide
theorem doubleAt_valid8 : ∀ op ∈ doubleAt 8 9 10, fopValid op := by decide
theorem addAt_valid8 : ∀ op ∈ addAt 8 9, fopValid op := by decide
theorem addAt_valid6 : ∀ op ∈ addAt 6 7, fopValid op := by decide

theorem doubleAt_eval0 (e : Env) :
    pt (evalOps (doubleAt 0 1 2) e) 0 1 2 = Proof.Ed448.double (pt e 0 1 2) := rfl

theorem doubleAt_eval8 (e : Env) :
    pt (evalOps (doubleAt 8 9 10) e) 8 9 10 = Proof.Ed448.double (pt e 8 9 10) := rfl

theorem addAt_eval8 (e : Env) :
    pt (evalOps (addAt 8 9) e) 3 4 5 = addWith (e 11) (pt e 0 1 2) (pt e 8 9 10) := rfl

theorem addAt_eval6 (e : Env) :
    pt (evalOps (addAt 6 7) e) 3 4 5 = addWith (e 11) (pt e 0 1 2) (pt e 6 7 10) := rfl

theorem doubleAt_keep0 (e : Env) (i : Index) (hi : 3 ≤ i.val ∧ i.val < 12 ∨ i.val = 20 ∨ i.val = 21) :
    evalOps (doubleAt 0 1 2) e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleAt 0 1 2, fopDest op < 3 ∨ (12 ≤ fopDest op ∧ fopDest op < 20) := by decide
    have := this op hop
    omega

theorem doubleAt_keep8 (e : Env) (i : Index)
    (hi : i.val < 8 ∨ i.val = 11 ∨ i.val = 20 ∨ i.val = 21) :
    evalOps (doubleAt 8 9 10) e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleAt 8 9 10, (8 ≤ fopDest op ∧ fopDest op < 11) ∨
        (12 ≤ fopDest op ∧ fopDest op < 20) := by decide
    have := this op hop
    omega

theorem addAt_keep (x y : Nat) (e : Env) (i : Index)
    (hi : i.val < 3 ∨ (6 ≤ i.val ∧ i.val < 12) ∨ i.val = 21) :
    evalOps (addAt x y) e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ x y, ∀ op ∈ addAt x y, (3 ≤ fopDest op ∧ fopDest op < 6) ∨
        (12 ≤ fopDest op ∧ fopDest op < 21) := by
      intro x y op hop
      simp only [addAt, List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [fopDest]
    have := this x y op hop
    omega

end VG.Proof.Ed448.X86_64

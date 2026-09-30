import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverParity

/-! Untrusted: canonical decoding checks y before reduction modulo p. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

theorem canonicalY_ok (s : State) (n : Nat) (hn : n < 2 ^ 255)
    (hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) = n) :
    WP isa (.block canonicalY) s fun t => (t.gpr .x8 == 0) = decide (n < Spec.X25519.P) ∧
      Keeps [.x10, .x11, .x21, .x22, .x23, .x24, .x8] s t := by
  have H := (add19_top (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
    (by rw [hv]; omega)).1
  have hz (w : Word) (hw : 0 - w = mask (decide (Spec.X25519.P ≤ n))) :
      (w == 0) = decide (n < Spec.X25519.P) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    have he : w = 0 ↔ mask (decide (Spec.X25519.P ≤ n)) = 0 := by
      rw [← hw]
      change w = 0#64 ↔ 0#64 - w = 0#64
      rw [BitVec.zero_sub, BitVec.neg_eq_zero_iff]
    rw [he]
    by_cases h : Spec.X25519.P ≤ n
    · simp only [decide_eq_true h, mask, ite_true]
      exact iff_of_false (by decide) (by omega)
    · simp only [decide_eq_false h, mask, Bool.false_eq_true, ite_false]
      exact iff_of_true True.intro (by omega)
  rw [hv] at H
  have H' := hz _ H
  apply WP.of_runBlock
  simp only [canonicalY, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, show 63 < Size.x.bits from by decide,
    show 16 * 0 < Size.w.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H' ⊢
    exact H'
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64

import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

/-- The 65 register-resident vector operations before iota. -/
theorem core_ok (s : VG.AArch64.State) (A : Spec.Sha3.State) (hA : Lanes s A) :
    WP isa (.block ((theta ++ rhoPi ++ chi).map Op.instr)) s fun s' =>
      Keep s s' ∧ CLanes (low s') A := by
  refine (ops_ok (theta ++ rhoPi ++ chi) s).mono fun s' h => ⟨h.1, ?_⟩
  rw [h.2]
  have ht := theta_lanes (low s) A hA
  have hd : DLanes (runLow theta (low s)) A := theta_d (low s) A hA
  have hr := rho_lanes (runLow theta (low s)) A ht hd
  have hc := chi_lanes (runLow rhoPi (runLow theta (low s))) A hr
  simpa only [runLow, List.foldl_append] using hc

theorem iota_ok (s : VG.AArch64.State) (A : Spec.Sha3.State) (rc : BitVec 64)
    (hA : CLanes (low s) A) (hc : s.gpr .x16 = rc) :
    WP isa (.block iota) s fun s' => Keep s s' ∧ Lanes s' (VG.Proof.Sha3.outState A rc) := by
  unfold iota
  refine WP.cons rfl (WP.cons rfl (wp_nil ⟨⟨rfl,rfl,rfl,rfl,rfl⟩, ?_⟩))
  intro i hi
  rw [← chiWord_out A rc i hi]
  have h0 : vreg i = .v0 ↔ i = 0 :=
    (show ∀ i < 25, vreg i = .v0 ↔ i = 0 by decide) i hi
  have h26 : vreg i ≠ .v26 := (show ∀ i < 25, vreg i ≠ .v26 by decide) i hi
  simp only [low, RegUpd.v_setV, reduceCtorEq, ite_false, ite_true, hc]
  simp only [h0, h26, ite_false]
  split
  · rename_i he
    subst i
    simpa only [low, vreg, List.getD_cons_zero, low_xor, vdword_ofVDwords_0] using congrArg (· ^^^ rc) (hA 0 (by decide))
  · exact hA i hi

theorem round_ok (r : Nat) (hr : r < 24) (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (hA : Lanes s A) :
    WP isa (.block (round r)) s fun s' => CoreKeep s s' ∧ Lanes s' (Spec.Sha3.rnd A r) := by
  unfold round
  rw [show constant (Spec.Sha3.RC r) ++ theta.map Op.instr ++ rhoPi.map Op.instr ++
      chi.map Op.instr ++ iota =
      constant (Spec.Sha3.RC r) ++ (theta ++ rhoPi ++ chi).map Op.instr ++ iota by
        simp only [List.map_append, List.append_assoc]]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (constant_ok (Spec.Sha3.RC r) s).mono fun s₁ h₁ => ?_
  have ha₁ : Lanes s₁ A := by
    intro i hi
    change vdword (s₁.v (vreg i)) 0 = _
    rw [h₁.2.1]
    exact hA i hi
  refine (core_ok s₁ A ha₁).mono fun s₂ h₂ => ?_
  have hrc : s₂.gpr .x16 = Spec.Sha3.RC r := by
    rw [h₂.1.gpr, h₁.2.2, constantLow_RC r hr]
  refine (iota_ok s₂ A (Spec.Sha3.RC r) h₂.2 hrc).mono fun s' h₃ => ?_
  refine ⟨h₁.1.trans (h₂.1.core.trans h₃.1.core), ?_⟩
  simpa only [VG.Proof.Sha3.outState_eq] using h₃.2

end VG.Proof.Sha3.AArch64.Sha3.Vector

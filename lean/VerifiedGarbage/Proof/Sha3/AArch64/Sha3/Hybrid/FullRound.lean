import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Rows

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid
open VG.Proof.Sha3 (outState outState_eq)

theorem roundConstant_ok (r : Nat) (s : VG.AArch64.State) :
    WP isa (.block (roundConstant r)) s fun s' =>
      s'.gpr .x16 = Spec.Sha3.RC r ∧ (∀ g, g ≠ .x16 → s'.gpr g = s.gpr g) ∧
      s'.v = s.v ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold roundConstant
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl (wp_nil ?_))))
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write_self, State.read, RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq]
    exact movz_movk64' _
  · intro g hg
    simp only [RegUpd.gpr_write, hg, ite_false]

theorem round_ok (r : Nat) (hr : r < 24) (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (hA : Lanes s r A) :
    WP isa (.block (round r)) s fun s' =>
      s'.gpr .x0 = s.gpr .x0 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Lanes s' (r + 1) (Spec.Sha3.rnd A r) := by
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine (roundConstant_ok r s).mono fun s₁ ⟨hrc, hg, hv, hm, hrd, hwr, hsp⟩ => ?_
  have ha₁ : Lanes s₁ r A := by
    intro i hi
    rw [value_congr (laneSlot (loc r i)) (fun v _ => by rw [hv]) (fun g he => hg g (by
      intro h; subst g
      exact slot_ne_g _ (loc_bound _ _ hi) _ gother_temps.2.2.1 he))]
    exact hA i hi
  refine (columns_ok r s₁ A ha₁).mono fun s₂ ⟨hk₂, ha₂, hc₂⟩ => ?_
  refine (rotations_ok r s₂ A ha₂ hc₂).mono fun s₃ ⟨hk₃, hb₃⟩ => ?_
  refine (rows_ok r hr s₃ A hb₃).mono fun s' ⟨hk₄, ha₄⟩ => ?_
  have hk := hk₂.trans (hk₃.trans hk₄)
  refine ⟨hk.x0.trans (hg _ (by decide)), hk.mem.trans hm, hk.rd.trans hrd,
    hk.wr.trans hwr, hk.sp.trans hsp, ?_⟩
  rwa [hk₃.x16, hk₂.x16, hrc, outState_eq] at ha₄

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

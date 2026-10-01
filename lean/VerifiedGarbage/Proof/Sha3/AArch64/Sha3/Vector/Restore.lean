import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

structure RestoreInv (orig s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : Keep s₀ s
  vals : ∀ i < k, s.v (vreg (8+i)) = orig.v (vreg (8+i))

theorem restore_ok (orig s₀ : VG.AArch64.State) (hs : Saved orig s₀.mem)
    (hptr : s₀.gpr .x1 = orig.gpr .x1)
    (hin : ∀ i < 8, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block restore) s₀ fun s' => Keep s₀ s' ∧
      ∀ r ∈ VG.AArch64.preservedV, (s'.v r).extractLsb' 0 64 = (orig.v r).extractLsb' 0 64 := by
  have hh : WP isa (.block restore) s₀ (RestoreInv orig s₀ 8) := by
    refine wp_range_flatMap (M := isa) (RestoreInv orig s₀) (fun i s hi hr => ?_)
      8 (Nat.le_refl _) s₀ ⟨Keep.refl _,fun _ h => absurd h (by omega)⟩
    unfold restoreReg
    refine WP.cons (exec_ldrq ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
    · rw [hr.keep.rd,hr.keep.wr,hr.keep.gpr]
      exact hin i hi
    · refine ⟨hr.keep.trans ⟨rfl,rfl,rfl,rfl,rfl⟩,fun j hj => ?_⟩
      rw [RegUpd.v_setV]
      simp only [vreg_inj (8+j) (by omega) (8+i) (by omega),Nat.add_left_cancel_iff]
      by_cases he : j = i
      · subst j
        simp only [ite_true,hr.keep.mem,hr.keep.gpr,hptr]
        exact hs i hi
      · rw [ite_eq_right (by omega)]
        exact hr.vals j (by omega)
  refine hh.mono fun s' h => ⟨h.keep,fun r hr => ?_⟩
  have hv : ∀ r ∈ VG.AArch64.preservedV, ∃ i : Fin 8, r = vreg (8+i.val) := by decide
  obtain ⟨i,rfl⟩ := hv r hr
  exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (h.vals i.val i.isLt)

end VG.Proof.Sha3.AArch64.Sha3.Vector

import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
set_option linter.unusedSimpArgs false

/-- The in-place cycle implements rho and pi for both independent states. -/
theorem rhoPi_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block rhoPi) s fun s' => VChg allV s s' ∧
      Pairs s' (Spec.Sha3.pi (Spec.Sha3.rho A)) (Spec.Sha3.pi (Spec.Sha3.rho B)) := by
  unfold rhoPi
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v25) rfl fun s₁ h1 => ?_
  have hcode : cycle.flatMap rhoPiStep = (List.range 24).flatMap
      (fun k => rhoPiStep (dest k,rotation k)) := by rfl
  rw [hcode]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VChg allV s₁ s' ∧ s'.v .v25 = ofVDwords A[source k]! B[source k]! ∧
      ∀ i < 25, s'.v (vreg i) = if Done k i then
        ofVDwords (Spec.Sha3.pi (Spec.Sha3.rho A))[i]! (Spec.Sha3.pi (Spec.Sha3.rho B))[i]!
        else ofVDwords A[i]! B[i]!)
    (fun k s' hk ⟨hchg,h25,hvals⟩ => ?_) 24 (Nat.le_refl _) s₁
    ⟨VChg.refl _ _,by rw [h1.v]; exact hp 1 (by decide),
      by intro i hi; rw [ite_eq_right (by simp [Done])];
         rw [h1.get (vreg i) (by
           change vreg i ≠ vreg 25; rw [ne_eq,vreg_inj i (by omega) 25 (by decide)]; omega)]
         exact hp i hi⟩)
    fun s₂ ⟨hchg,_,vals⟩ => ⟨(h1.chg.trans hchg).mono (fun r _ => allV_mem r),?_⟩
  · obtain ⟨hd,hs,hk0,hkr,hfresh,hnext,_,_⟩ := cycle_facts k hk
    refine WP.mono (rhoPiStep_ok hd hk0 hkr) fun s'' ⟨hstep,hnew,htemp⟩ =>
      ⟨(hchg.trans hstep).mono (fun r _ => allV_mem r),?_,?_⟩
    · rw [htemp,hvals _ hd,ite_eq_right hfresh,hnext]
    · intro i hi
      by_cases he : i = dest k
      · subst i
        rw [hnew,h25,vdword_ofVDwords_0,vdword_ofVDwords_1,
          ← cycle_word A hk,← cycle_word B hk,ite_eq_left ((done_next k _).mpr (Or.inr rfl))]
      · have h25n : vreg i ≠ VReg.v25 := by
          change vreg i ≠ vreg 25
          rw [ne_eq,vreg_inj i (by omega) 25 (by decide)]; omega
        have h26n : vreg i ≠ VReg.v26 := by
          change vreg i ≠ vreg 26
          rw [ne_eq,vreg_inj i (by omega) 26 (by decide)]; omega
        rw [hstep.get (vreg i) (by
          simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or]
          exact ⟨by rw [vreg_inj i (by omega) (dest k) (by omega)]; exact he,h25n,h26n⟩),hvals i hi]
        have hiff : Done (k+1) i ↔ Done k i := by rw [done_next,or_iff_left he]
        by_cases hd : Done k i
        · rw [ite_eq_left hd,ite_eq_left (hiff.mpr hd)]
        · rw [ite_eq_right hd,ite_eq_right (fun h => hd (hiff.mp h))]
  · intro i hi
    rw [vals i hi]
    by_cases he : i = 0
    · subst i
      rw [ite_eq_right (by rw [done_all 0 (by decide)]; simp),cycle_zero A,cycle_zero B]
    · rw [ite_eq_left ((done_all i hi).mpr he)]
end VG.Proof.Sha3.AArch64.Neon

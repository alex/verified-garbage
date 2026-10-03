import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VChg)

/-- The canonical chi word, expressed in the operand order used by BIC. -/
theorem chi_word (A : Spec.Sha3.State) {x y : Nat} (hx : x < 5) (hy : y < 5) :
    (Spec.Sha3.chi A)[x+5*y]! = A[x+5*y]! ^^^
      (A[(x+2)%5+5*y]! &&& ~~~(A[(x+1)%5+5*y]!)) := by
  rw [VG.Proof.Sha3.getElem!_eq _ (by omega),VG.Proof.Sha3.chi_get A hx hy,
    VG.Proof.Sha3.getElem!_eq A (by omega),VG.Proof.Sha3.getElem!_eq A (by omega),
    VG.Proof.Sha3.getElem!_eq A (by omega),BitVec.and_comm]

/-- Preserve and transform one complete chi row for two states. -/
theorem row_ok {s : State} {A B : Spec.Sha3.State} {y : Nat} (hy : y < 5)
    (hp : ∀ x < 5, s.v (vreg (x+5*y)) = ofVDwords A[x+5*y]! B[x+5*y]!) :
    WP isa (.block (row y)) s fun s' => VChg allV s s' ∧
      ∀ i < 25, s'.v (vreg i) = if i/5 = y then
        ofVDwords (Spec.Sha3.chi A)[i]! (Spec.Sha3.chi B)[i]! else s.v (vreg i) := by
  have hn : ∀ i < 25, vreg i ∉ [VReg.v25,.v26,.v27,.v28,.v29] := by decide
  have ht30 : ∀ z < 5, vreg (25+z) ≠ VReg.v30 := by decide
  have htstate : ∀ z < 5, ∀ i < 25, vreg (25+z) ≠ vreg i := by decide
  have hi30 : ∀ i < 25, vreg i ≠ VReg.v30 := by decide
  unfold row
  rw [WP.block_append_iff]
  refine WP.mono (saveRow_ok hy) fun s₁ ⟨h1,vals1⟩ => ?_
  have cols1 : ∀ z < 5, s₁.v (vreg (25+z)) = ofVDwords A[z+5*y]! B[z+5*y]! := by
    intro z hz; rw [vals1 z hz]; exact hp z hz
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VChg allV s₁ s' ∧
      (∀ z < 5, s'.v (vreg (25+z)) = ofVDwords A[z+5*y]! B[z+5*y]!) ∧
      ∀ i < 25, s'.v (vreg i) = if i/5 = y ∧ i%5 < k then
        ofVDwords (Spec.Sha3.chi A)[i]! (Spec.Sha3.chi B)[i]! else s₁.v (vreg i))
    (fun k s' hk ⟨hchg,hcols,hvals⟩ => ?_) 5 (Nat.le_refl _) s₁
    ⟨VChg.refl _ _,cols1,by intro i hi; rw [ite_eq_right (by omega)]⟩)
    fun s₂ ⟨hchg,_,vals⟩ => ⟨(h1.trans hchg).mono (fun r _ => allV_mem r),?_⟩
  · refine WP.mono (chiWord_ok hk hy hcols) fun s'' ⟨hstep,hnew⟩ =>
      ⟨(hchg.trans hstep).mono (fun r _ => allV_mem r),?_,?_⟩
    · intro z hz
      rw [hstep.get _ (by
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
        exact ⟨ht30 z hz,htstate z hz _ (by omega)⟩)]
      exact hcols z hz
    · intro i hi
      by_cases he : i = k+5*y
      · subst i
        rw [hnew,← chi_word A hk hy,← chi_word B hk hy,ite_eq_left (by omega)]
      · rw [hstep.get _ (by
          simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨hi30 i hi,by rw [vreg_inj i (by omega) (k+5*y) (by omega)]; exact he⟩),hvals i hi]
        have hne : ¬ (i/5 = y ∧ i%5 = k) := by intro h; omega
        by_cases h : i/5 = y ∧ i%5 < k <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
  · intro i hi
    rw [vals i hi,h1.get _ (hn i hi)]
    have hmod : i%5 < 5 := by omega
    simp only [hmod,and_true]
end VG.Proof.Sha3.AArch64.Neon

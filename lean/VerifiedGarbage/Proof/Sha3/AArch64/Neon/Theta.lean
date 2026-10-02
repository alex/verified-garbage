import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.Sha3 (C D)

/-- Internal kernels may use every vector register; their boundaries save the ABI-preserved lanes. -/
def allV : List VReg := (List.range 32).map vreg

theorem allV_mem : ∀ r : VReg, r ∈ allV := by intro r; cases r <;> decide

/-- Theta acts independently on the two states held in NEON lanes. -/
theorem theta_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block theta) s fun s' => VChg allV s s' ∧ Pairs s' (Spec.Sha3.theta A) (Spec.Sha3.theta B) := by
  unfold theta
  rw [WP.block_append_iff]
  refine WP.mono (parityAll_ok hp) fun s₁ ⟨h1,hp1,cols1⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => VChg allV s₁ s' ∧
      (∀ c < 5, s'.v (vreg (25+c)) = ofVDwords (C A c) (C B c)) ∧
      ∀ i < 25, s'.v (vreg i) = if i%5 < k then
        ofVDwords (A[i]! ^^^ D A (i%5)) (B[i]! ^^^ D B (i%5)) else ofVDwords A[i]! B[i]!)
    (fun k s' hk ⟨hkeep,hcols,hvals⟩ => ?_) 5 (Nat.le_refl _) s₁
    ⟨VChg.refl _ _,cols1,by intro i hi; rw [ite_eq_right (Nat.not_lt_zero _)]; exact hp1 i hi⟩)
    fun s₂ ⟨hkeep,_,hvals⟩ => ⟨(h1.trans hkeep).mono (fun r _ => allV_mem r),?_⟩
  · refine WP.mono (correction_ok hk hcols) fun s'' ⟨hchg,hcols',vals⟩ =>
      ⟨(hkeep.trans hchg).mono (fun r _ => allV_mem r),hcols',?_⟩
    intro i hi
    rw [vals i hi,hvals i hi]
    by_cases he : i%5 = k
    · rw [ite_eq_left he,ite_eq_right (by omega),ite_eq_left (by omega),pair_xor,he]
    · rw [ite_eq_right he]
      by_cases hlt : i%5 < k <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
  · intro i hi
    rw [hvals i hi,ite_eq_left (by omega)]
    have hta := VG.Proof.Sha3.theta_get A hi
    have htb := VG.Proof.Sha3.theta_get B hi
    rw [VG.Proof.Sha3.getElem!_eq A hi,VG.Proof.Sha3.getElem!_eq B hi,
      ← hta,← htb,VG.Proof.Sha3.getElem!_eq (Spec.Sha3.theta A) hi,
      VG.Proof.Sha3.getElem!_eq (Spec.Sha3.theta B) hi]
end VG.Proof.Sha3.AArch64.Neon

import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VChg)

/-- Chi's nonlinear layer acts independently on the paired states. -/
theorem chi_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block chi) s fun s' => VChg allV s s' ∧ Pairs s' (Spec.Sha3.chi A) (Spec.Sha3.chi B) := by
  unfold chi
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun y s' => VChg allV s s' ∧ ∀ i < 25, s'.v (vreg i) = if i/5 < y then
      ofVDwords (Spec.Sha3.chi A)[i]! (Spec.Sha3.chi B)[i]! else ofVDwords A[i]! B[i]!)
    (fun y s' hy ⟨hchg,hvals⟩ => ?_) 5 (Nat.le_refl _) s
    ⟨VChg.refl _ _,by intro i hi; rw [ite_eq_right (Nat.not_lt_zero _)]; exact hp i hi⟩)
    fun s' ⟨hchg,hvals⟩ => ⟨hchg,fun i hi => by rw [hvals i hi,ite_eq_left (by omega)]⟩
  refine WP.mono (row_ok hy (A := A) (B := B) (by
    intro x hx
    rw [hvals _ (by omega),ite_eq_right (by omega)])) fun s'' ⟨hrow,vals⟩ =>
      ⟨(hchg.trans hrow).mono (fun r _ => allV_mem r),?_⟩
  intro i hi
  rw [vals i hi,hvals i hi]
  by_cases he : i/5 = y
  · rw [ite_eq_left he,ite_eq_left (by omega)]
  · rw [ite_eq_right he]
    by_cases hlt : i/5 < y <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
end VG.Proof.Sha3.AArch64.Neon

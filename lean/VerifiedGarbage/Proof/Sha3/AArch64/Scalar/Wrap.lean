import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Save
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Load
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Restore
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

/-- The middle may use every GPR but must retain public pointers, saved GPRs,
and the ABI-protected vector registers. -/
structure CoreState (orig : VG.AArch64.State) (A : Spec.Sha3.State) (s : VG.AArch64.State) : Prop where
  keep : Keep orig s
  ptrs : Ptrs orig s
  saved : Saved orig s.mem
  vec : ∀ r ∈ preservedV, s.v r = orig.v r
  lanes : Lanes s A

theorem wrap_correct (middle : Prog isa)
    (hmid : ∀ orig A s, VG.Proof.Sha3.AArch64.Pre orig → CoreState orig A s →
      WP isa middle s (CoreState orig (Spec.Sha3.keccakF A)))
    (orig : VG.AArch64.State) (hp : VG.Proof.Sha3.AArch64.Pre orig) :
    WP isa (wrap middle) orig fun s' => abiPreserved orig s' ∧
      VG.Proof.Sha3.permuteAArch64.post orig s' := by
  unfold wrap
  rw [WP.seq_iff]
  refine (save_ok orig hp).mono fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  refine (load_ok s₁ (fun i hi => ?_)).mono fun s₂ h₂ => ?_
  · rw [h₁.1.rd,h₁.1.wr,h₁.2.1]
    exact hp.in_all (hp.lane_in (.inl rfl) hi)
  · have ha : Lanes s₂ (Spec.Sha3.stateAt orig.mem (orig.gpr .x0)) := by
      have hst := VG.Proof.Sha3.AArch64.Sha3.Vector.state_frame orig s₁ hp
        (congrFun h₁.2.1 .x0) h₁.2.2.1
      rw [hst] at h₂
      exact h₂.2.2.2
    have hs₂ : CoreState orig (Spec.Sha3.stateAt orig.mem (orig.gpr .x0)) s₂ := by
      refine ⟨h₁.1.trans h₂.1,?_,?_,?_,ha⟩
      · simpa only [Ptrs,h₂.2.2.1] using h₁.2.2.2.2.1
      · simpa only [h₂.2.1] using h₁.2.2.2.1
      · intro r hr
        rw [h₂.2.2.1]
        have hn : ∀ r ∈ preservedV, r ≠ .v30 ∧ r ≠ .v31 := by decide
        exact h₁.2.2.2.2.2 r (hn r hr).1 (hn r hr).2
    rw [WP.seq_iff]
    refine (hmid orig _ s₂ hp hs₂).mono fun s₃ h₃ => ?_
    rw [WP.seq_iff]
    refine (store_ok s₃ (orig.gpr .x0) _ h₃.lanes h₃.ptrs.1 (fun i hi => ?_)).mono
      fun s₄ h₄ => ?_
    · rw [h₃.keep.wr]
      exact hp.lane_in (.inl rfl) hi
    · have hs₄ : Saved orig s₄.mem := by
        intro i hi
        rw [h₄.2.2.1.readW (scratch_contains orig hi) ?_ (by decide)]
        · exact h₃.saved i hi
        · simpa only [List.mem_singleton,forall_eq] using hp.st_scr.symm
      refine (restore_ok orig s₄ hs₄ ?_ (fun i hi => ?_)).mono fun s' h₅ => ?_
      · simpa only [h₄.2.1] using h₃.ptrs.2
      · rw [h₄.1.rd,h₄.1.wr,h₃.keep.rd,h₃.keep.wr]
        exact hp.in_all (hp.in_wr (.inr rfl) (scratch_contains orig hi))
      · refine ⟨⟨h₅.2.2.2,h₅.1.sp.trans (h₄.1.sp.trans h₃.keep.sp),?_⟩,?_⟩
        · intro r hr
          rw [h₅.2.2.1,h₄.2.1,h₃.vec r hr]
        · change Spec.Sha3.stateAt s'.mem (orig.gpr .x0) = _
          rw [h₅.2.1]
          exact h₄.2.2.2

end VG.Proof.Sha3.AArch64.Scalar.Boundary

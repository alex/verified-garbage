import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ControlLoop
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec

namespace VG.Proof.Sha3.AArch64.Scalar.Control
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64.Scalar.Boundary

/-- Vector temporary lanes preserve the counted loop's complete invariant. -/
theorem vector_core_ready_ok (orig : State) (A : Spec.Sha3.State) (k : Nat) (s : State)
    (_hp : VG.Proof.Sha3.AArch64.Pre orig) (hs : Ready orig A k s) :
    WP isa (.block vectorCoreInstrs) s
      (Ready orig (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A)))) k) := by
  obtain ⟨t, ht, hl, hm, hrd, hwr, hsp, hv⟩ := vector_core_ok A s hs.core.lanes
  apply WP.of_runBlock
  refine ⟨t, ht, ?_⟩
  refine ⟨⟨⟨hrd.trans hs.core.keep.rd,hwr.trans hs.core.keep.wr,
    hsp.trans hs.core.keep.sp⟩,?_,?_,?_,hl⟩,?_,?_,?_⟩
  · simpa only [Ptrs,hv .v30 (by decide) (by decide) (by decide) (by decide),
      hv .v31 (by decide) (by decide) (by decide) (by decide)] using hs.core.ptrs
  · intro i hi
    have hn : ∀ i < 11, VG.Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v24 ∧
        VG.Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v25 ∧
        VG.Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v28 ∧
        VG.Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v29 := by decide
    rw [show vdword (t.v (VG.Impl.Sha3.AArch64.Scalar.Boundary.savedVec i)) 0 =
      vdword (s.v (VG.Impl.Sha3.AArch64.Scalar.Boundary.savedVec i)) 0 from
        congrArg (fun v => vdword v 0)
          (hv _ (hn i hi).1 (hn i hi).2.1 (hn i hi).2.2.1 (hn i hi).2.2.2)]
    exact hs.core.saved i hi
  · intro r hr
    have hn : ∀ r ∈ preservedV, r ≠ .v24 ∧ r ≠ .v25 ∧ r ≠ .v28 ∧ r ≠ .v29 := by decide
    rw [hv r (hn r hr).1 (hn r hr).2.1 (hn r hr).2.2.1 (hn r hr).2.2.2]
    exact hs.core.vec r hr
  · intro i hi
    rw [hm]
    exact hs.constants i hi
  · rw [hv .v26 (by decide) (by decide) (by decide) (by decide)]
    exact hs.next
  · rw [hv .v27 (by decide) (by decide) (by decide) (by decide)]
    exact hs.limit

theorem middle_vector_ok (orig : State) (A : Spec.Sha3.State) (s : State)
    (hp : VG.Proof.Sha3.AArch64.Pre orig) (hs : CoreState orig A s) :
    WP isa (VG.Impl.Sha3.AArch64.Scalar.Control.middle vectorCoreInstrs) s
      (CoreState orig (Spec.Sha3.keccakF A)) :=
  middle_ok vectorCoreInstrs vector_core_ready_ok orig A s hp hs

end VG.Proof.Sha3.AArch64.Scalar.Control

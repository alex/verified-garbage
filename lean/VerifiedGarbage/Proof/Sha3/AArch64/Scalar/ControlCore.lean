import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ControlLoop
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.CoreExec

namespace VG.Proof.Sha3.AArch64.Scalar.Control
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64.Scalar.Boundary

/-- The concrete round core preserves the saved ABI words, round constants,
and public pointers used by the counted loop. -/
theorem core_ready_ok (orig : State) (A : Spec.Sha3.State) (k : Nat) (s : State)
    (hp : VG.Proof.Sha3.AArch64.Pre orig) (hs : Ready orig A k s) :
    WP isa (.block coreInstrs) s
      (Ready orig (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A)))) k) := by
  have hw : SlotsWritable (orig.gpr .x1) s := by
    intro i hi
    rw [hs.core.keep.wr]
    exact hp.in_wr (.inr rfl) (Offset.contains_base _
      (by unfold lowerSpillOffset; omega) (by unfold lowerSpillOffset; omega))
  obtain ⟨t, ht, hl, hrd, hwr, hsp, hf, hv⟩ :=
    core_ok A (orig.gpr .x1) s hs.core.lanes hs.core.ptrs.2 hw
  apply WP.of_runBlock
  refine ⟨t, ht, ?_⟩
  refine ⟨⟨⟨hrd.trans hs.core.keep.rd,hwr.trans hs.core.keep.wr,
    hsp.trans hs.core.keep.sp⟩,?_,?_,?_,hl⟩,?_,?_,?_⟩
  · simpa only [Ptrs,hv .v30 (by decide) (by decide),hv .v31 (by decide) (by decide)]
      using hs.core.ptrs
  · intro i hi
    rw [spill_frame_readW hf (8*i) (.inl (by omega)) (by omega)]
    exact hs.core.saved i hi
  · intro r hr
    have hn : ∀ r ∈ preservedV, r ≠ .v28 ∧ r ≠ .v29 := by decide
    rw [hv r (hn r hr).1 (hn r hr).2]
    exact hs.core.vec r hr
  · intro i hi
    unfold constAddr
    rw [spill_frame_readW hf (128+8*i) (.inr (by omega)) (by omega)]
    exact hs.constants i hi
  · rw [hv .v26 (by decide) (by decide)]
    exact hs.next
  · rw [hv .v27 (by decide) (by decide)]
    exact hs.limit

theorem middle_core_ok (orig : State) (A : Spec.Sha3.State) (s : State)
    (hp : VG.Proof.Sha3.AArch64.Pre orig) (hs : CoreState orig A s) :
    WP isa (VG.Impl.Sha3.AArch64.Scalar.Control.middle coreInstrs) s
      (CoreState orig (Spec.Sha3.keccakF A)) :=
  middle_ok coreInstrs core_ready_ok orig A s hp hs

end VG.Proof.Sha3.AArch64.Scalar.Control

import VerifiedGarbage.Impl.Argon2.X86_64.FinalReduction
import VerifiedGarbage.Proof.Argon2.X86_64.ReductionInit
import VerifiedGarbage.Proof.Argon2.X86_64.ReductionInitCT

/-! Complete final block reduction, including setup, termination and a public trace. -/

namespace VG.Proof.Argon2.X86_64.FinalReduction

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

theorem code_ok (s : State) (p : Params) (h : ReductionInit.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.X86_64.FinalReduction.code s
      (ReduceLanes.Finished s · p memory (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock)) := by
  unfold Impl.Argon2.X86_64.FinalReduction.code
  refine WP.seq ((ReductionInit.code_ok s p h memory represented).mono ?_)
  intro a prepared
  refine (ReduceLanes.loop_ok p.lanes a p 0 prepared.ready memory zeroBlock prepared.represented
    h.allocation.positive (Nat.zero_add _)).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.base.trans prepared.base, finished.laneWord,
    finished.rd.trans prepared.rd, finished.wr.trans prepared.wr, ?_, finished.mxcsr.trans prepared.mxcsr, ?_⟩
  · have frame := finished.frame
    rw [prepared.base] at frame
    exact prepared.frame.trans frame
  · intro r hr bx; exact (finished.regs r hr bx).trans (prepared.regs r hr bx)

theorem code_rel (p : Params) (positive : 0 < p.lanes) (leftMemory rightMemory : Array Block) :
    RelCT isa (ReductionInit.Related p leftMemory rightMemory) Impl.Argon2.X86_64.FinalReduction.code
      (fun _ _ => True) :=
  (ReductionInit.code_rel p leftMemory rightMemory).seq
    (ReduceLanes.loop_rel p 0 p.lanes leftMemory rightMemory zeroBlock zeroBlock positive (Nat.zero_add _))

end VG.Proof.Argon2.X86_64.FinalReduction

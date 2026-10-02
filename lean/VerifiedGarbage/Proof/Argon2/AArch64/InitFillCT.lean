import VerifiedGarbage.Proof.Argon2.AArch64.InitFill
import VerifiedGarbage.Proof.Argon2.AArch64.FillFinishCT

/-! The entire post-H₀ pipeline leaks only the reviewed complete filling reference log. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def initial (p : Params) (s : State) : FillState := initMemory p (bytesAt s.mem (s.gpr .x19) 64)

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (initial p t)).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.AArch64.InitFill.code name v.hash) (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  have params := hp.left.environment.parameters
  have q : 2 ≤ p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega
  have lanesBound : p.lanes < 2 ^ 64 := Nat.lt_trans params.lanesBound (by decide)
  have pub : MemoryInit.AgreeBases s t := by
    refine ⟨hp.stacks, ?_⟩
    intro r hr
    simp only [MemoryInit.publicBases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.bases
    · exact hp.left.scratch.trans (hp.works.trans hp.right.scratch.symm)
    · exact hp.left.initializing.laneLength.trans hp.right.initializing.laneLength.symm
  have rightReady : MemoryInit.Ready (FillKernel.matrix s) p.lanes p.laneLen t := by
    rw [hp.matrices]; exact hp.right.initializing
  cases ea with
  | seq initA restA =>
    cases eb with
    | seq initB restB =>
      have initTrace := MemoryInit.code_ct v name (FillKernel.matrix s) p.lanes p.laneLen
        params.lanesPositive lanesBound q _ _ _ _ _ _ hp.left.initializing rightReady pub initA initB
      obtain ⟨_, sa, runA, doneA⟩ := MemoryInit.complete_ok v name s (FillKernel.matrix s) p.lanes p.laneLen
        hp.left.initializing params.lanesPositive lanesBound q
      obtain ⟨_, sb, runB, doneB⟩ := MemoryInit.complete_ok v name t (FillKernel.matrix t) p.lanes p.laneLen
        hp.right.initializing params.lanesPositive lanesBound q
      obtain ⟨_, rfl⟩ := Exec.det initA runA
      obtain ⟨_, rfl⟩ := Exec.det initB runB
      cases restA with
      | seq setupA fillA =>
        cases restB with
        | seq setupB fillB =>
          have bases := doneA.bp.trans (hp.bases.trans doneB.bp.symm)
          obtain ⟨setupTrace, _⟩ := FillSetup.code_rel _ _ _ _ _ _ ⟨bases, doneA.sp.trans (hp.stacks.trans doneB.sp.symm)⟩ setupA setupB
          obtain ⟨_, ca, runA, preparedA⟩ := FillSetup.code_ok _ p (initialized_setup hp.left doneA)
          obtain ⟨_, cb, runB, preparedB⟩ := FillSetup.code_ok _ p (initialized_setup hp.right doneB)
          obtain ⟨_, rfl⟩ := Exec.det setupA runA
          obtain ⟨_, rfl⟩ := Exec.det setupB runB
          have preparedBases := (preparedA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)).trans
            (bases.trans (preparedB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)).symm)
          have preparedStacks := preparedA.sp.trans
            ((doneA.sp.trans (hp.stacks.trans doneB.sp.symm)).trans
              preparedB.sp.symm)
          have initMatrices := (doneA.frame_word hp.left.initializing.space 232 (by decide) (Or.inr (by decide))).trans
            (hp.matrices.trans (doneB.frame_word hp.right.initializing.space 232 (by decide) (Or.inr (by decide))).symm)
          have matrices := preparedA.matrix.trans (initMatrices.trans preparedB.matrix.symm)
          have initOutputs := (doneA.frame_word hp.left.initializing.space 256 (by decide) (Or.inr (by decide))).trans
            (hp.outputs.trans (doneB.frame_word hp.right.initializing.space 256 (by decide) (Or.inr (by decide))).symm)
          have outputs := (preparedA.words 256 (by decide) (by decide)).trans
            (initOutputs.trans (preparedB.words 256 (by decide) (by decide)).symm)
          have initWorks := (doneA.frame_word hp.left.initializing.space 248 (by decide) (Or.inr (by decide))).trans
            (hp.works.trans (doneB.frame_word hp.right.initializing.space 248 (by decide) (Or.inr (by decide))).symm)
          have works := (preparedA.words 248 (by decide) (by decide)).trans
            (initWorks.trans (preparedB.words 248 (by decide) (by decide)).symm)
          have related : FillFinish.Related p (initial p s) (initial p t) _ _ :=
            ⟨preparedA.finish_ready (initialized_setup hp.left doneA) (initialized_output hp.left doneA) hp.left.positive,
              preparedB.finish_ready (initialized_setup hp.right doneB) (initialized_output hp.right doneB) hp.right.positive,
              preparedBases, preparedStacks, matrices, outputs, works,
              preparedA.represents (initialized_setup hp.left doneA) _ (initialized_represents hp.left doneA),
              preparedB.represents (initialized_setup hp.right doneB) _ (initialized_represents hp.right doneB), hp.indices⟩
          obtain ⟨fillTrace, _⟩ := FillFinish.code_rel v name p (initial p s) (initial p t) _ _ _ _ _ _ related fillA fillB
          exact ⟨by rw [initTrace, setupTrace, fillTrace], trivial⟩

end VG.Proof.Argon2.AArch64.InitFill

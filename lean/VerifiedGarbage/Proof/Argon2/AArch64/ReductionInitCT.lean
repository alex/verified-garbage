import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Argon2.AArch64.ReductionInit
import VerifiedGarbage.Proof.Argon2.AArch64.ReduceLanesCT
import VerifiedGarbage.Proof.Argon2.AArch64.ClearBlockLit

/-! Clearing the accumulator follows public pointers and visits a fixed block. -/

namespace VG.Proof.Argon2.AArch64.ReductionInit

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem setup_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.ReductionInit.setup) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem clear_rel : RelCT isa (fun s t => s.gpr .x0 = t.gpr .x0 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.ClearBlock.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_rel (p : Params) (leftMemory rightMemory : Array Block) :
    RelCT isa (Related p leftMemory rightMemory) Impl.Argon2.AArch64.ReductionInit.code
      (ReduceLanes.Related p 0 leftMemory rightMemory zeroBlock zeroBlock) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA clearA =>
    cases eb with
    | seq setupB clearB =>
      obtain ⟨setupTrace, setupSp⟩ := setup_rel _ _ _ _ _ _ ⟨hp.bases, hp.stacks⟩ setupA setupB
      obtain ⟨_, sa, runA, destA, _, _⟩ := setup_ok s hp.left.allocation.read
      obtain ⟨_, sb, runB, destB, _, _⟩ := setup_ok t hp.right.allocation.read
      obtain ⟨_, rfl⟩ := Exec.det setupA runA
      obtain ⟨_, rfl⟩ := Exec.det setupB runB
      obtain ⟨clearTrace, _⟩ := clear_rel _ _ _ _ _ _ ⟨destA.trans (hp.matrices.trans destB.symm), setupSp⟩ clearA clearB
      obtain ⟨_, a', runA, doneA⟩ := code_ok s p hp.left leftMemory hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := code_ok t p hp.right rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupA clearA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupB clearB) runB
      refine ⟨by rw [setupTrace, clearTrace], doneA.ready, doneB.ready, ?_, doneA.sp.trans (hp.stacks.trans doneB.sp.symm),
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
        (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm)

end VG.Proof.Argon2.AArch64.ReductionInit

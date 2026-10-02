import VerifiedGarbage.Proof.Argon2.X86_64.FillIterationsBody
import VerifiedGarbage.Proof.Argon2.X86_64.FillIterationCT

/-! Iteration advances its public pass counter and retains the reviewed filling log. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillIterations

theorem advance_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) advance (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

structure NextRelated (p : Params) (pass : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass s
  right : Ready p pass t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => NextRelated p pass leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) body
      (fun s t => s.cf = t.cf ∧ (pass + 1 < p.passes → NextRelated p (pass + 1)
        (fillPass p leftState pass)
        (fillPass p rightState pass) s t)) := by
  intro s t ts tt a b hp ea eb
  obtain ⟨hp, indices⟩ := hp
  have related : FillIteration.Related p pass leftState rightState s t :=
    ⟨hp.left.filling, hp.right.filling, hp.bases, hp.stacks, hp.matrices, hp.work, hp.leftMatrix, hp.rightMatrix, indices⟩
  cases ea with
  | seq segmentA advanceA =>
    cases eb with
    | seq segmentB advanceB =>
      obtain ⟨segmentTrace, _⟩ := FillIteration.code_rel p pass leftState rightState
        _ _ _ _ _ _ related segmentA segmentB
      obtain ⟨_, sa, runA, filledA⟩ := FillIteration.code_ok s p pass hp.left.filling leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := FillIteration.code_ok t p pass hp.right.filling rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det segmentA runA
      obtain ⟨_, rfl⟩ := Exec.det segmentB runB
      have bases := (filledA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
        (hp.bases.trans (filledB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ bases advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentB advanceB) runB
      refine ⟨by rw [segmentTrace, advancedTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.work.trans doneB.work.symm), doneA.represented, doneB.represented⟩
      · exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
          (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)
      · exact (doneA.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
          (hp.stacks.trans (doneB.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)

end VG.Proof.Argon2.X86_64.FillIterations

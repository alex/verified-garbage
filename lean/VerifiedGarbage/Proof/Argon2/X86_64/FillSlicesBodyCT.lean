import VerifiedGarbage.Proof.Argon2.X86_64.FillSlicesBody
import VerifiedGarbage.Proof.Argon2.X86_64.FillSliceCT

/-! A slice iteration preserves public allocations and its public continuation guard. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSlices

theorem advance_rel : RelCT isa (fun _ _ : State => True) (.block advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

structure NextRelated (p : Params) (pass slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : FillSlice.Ready p pass slice s
  right : FillSlice.Ready p pass slice t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass slice : Nat) (leftState rightState : FillState) :
    RelCT isa (FillSlice.Related p pass slice leftState rightState) body
      (fun s t => s.cf = t.cf ∧ (slice + 1 < 4 → NextRelated p pass (slice + 1)
        (Proof.Argon2.lanes p pass slice 0 p.lanes leftState) (Proof.Argon2.lanes p pass slice 0 p.lanes rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq sliceA advanceA =>
    cases eb with
    | seq sliceB advanceB =>
      obtain ⟨sliceTrace, _⟩ := FillSlice.code_rel p pass slice leftState rightState _ _ _ _ _ _ hp sliceA sliceB
      obtain ⟨advanceTrace, _⟩ := advance_rel _ _ _ _ _ _ trivial advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass slice hp.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass slice hp.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq sliceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq sliceB advanceB) runB
      refine ⟨by rw [sliceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.work.trans doneB.work.symm), doneA.represented, doneB.represented⟩
      · exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
          (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)
      · exact (doneA.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans
          (hp.stacks.trans (doneB.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).symm)

end VG.Proof.Argon2.X86_64.FillSlices

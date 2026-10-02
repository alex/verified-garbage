import VerifiedGarbage.Proof.Argon2.X86_64.FillLanesBody
import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupCT

/-! Lane iteration preserves public allocations and loops on the public lane count. -/

namespace VG.Proof.Argon2.X86_64.FillLanes

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillLanes

theorem advance_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) (.block advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

structure NextRelated (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  ready : SegmentSetup.RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (SegmentSetup.Related p pass lane slice leftState rightState) body
      (fun s t => s.cf = t.cf ∧ (lane + 1 < p.lanes → NextRelated p pass (lane + 1) slice
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen leftState)
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq segmentA advanceA =>
    cases eb with
    | seq segmentB advanceB =>
      obtain ⟨segmentTrace, _⟩ := SegmentSetup.code_rel p pass lane slice leftState rightState
        _ _ _ _ _ _ hp segmentA segmentB
      obtain ⟨_, sa, runA, filledA⟩ := SegmentSetup.code_ok s p pass lane slice hp.ready.left leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := SegmentSetup.code_ok t p pass lane slice hp.ready.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det segmentA runA
      obtain ⟨_, rfl⟩ := Exec.det segmentB runB
      have bases := (filledA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
        (hp.ready.bases.trans (filledB.regs .rbp (by simp [calleeSaved]) (by decide)).symm)
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ bases advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p pass lane slice hp.ready.left leftState hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p pass lane slice hp.ready.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq segmentB advanceB) runB
      refine ⟨by rw [segmentTrace, advancedTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨⟨doneA.next active, doneB.next active, ?_, ?_,
        doneA.matrix.trans (hp.ready.matrices.trans doneB.matrix.symm),
        doneA.work.trans (hp.ready.work.trans doneB.work.symm)⟩, doneA.represented, doneB.represented⟩
      · exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide) (by decide)).trans
          (hp.ready.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide) (by decide)).symm)
      · exact (doneA.regs .rsp (by simp [calleeSaved]) (by decide) (by decide)).trans
          (hp.ready.stacks.trans (doneB.regs .rsp (by simp [calleeSaved]) (by decide) (by decide)).symm)

end VG.Proof.Argon2.X86_64.FillLanes

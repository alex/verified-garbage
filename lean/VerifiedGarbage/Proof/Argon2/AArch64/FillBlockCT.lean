import VerifiedGarbage.Proof.Argon2.AArch64.FillBlock
import VerifiedGarbage.Proof.Argon2.AArch64.RandomSourceCT
import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelCT

/-! An active filling cell leaks only its specified data-dependent reference. -/

namespace VG.Proof.Argon2.AArch64.FillBlock

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  source : RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  references : independent p pass slice = false →
    reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index leftState.memory) =
      reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index rightState.memory)

theorem Related.of_indices {p : Params} {pass lane slice index old : Nat} {s t : State}
    {leftState rightState : FillState} (source : RandomSource.Related p pass lane slice index old s t)
    (leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory)
    (rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory)
    (indices : (fillBlock p pass slice lane index leftState).indices =
      (fillBlock p pass slice lane index rightState).indices) :
    Related p pass lane slice index old leftState rightState s t := by
  refine ⟨source, leftMatrix, rightMatrix, ?_⟩
  intro mode
  rw [Proof.Argon2.FillStep.indices p pass lane slice index leftState source.left.filling.bounds.active,
    Proof.Argon2.FillStep.indices p pass lane slice index rightState source.right.filling.bounds.active] at indices
  simp only [mode, Bool.false_eq_true, ite_false] at indices
  exact (List.cons.inj indices).1

theorem Related.reference_eq {p : Params} {pass lane slice index old : Nat} {s t : State}
    {leftState rightState : FillState} (h : Related p pass lane slice index old leftState rightState s t) :
    reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index leftState.memory) =
      reference p pass lane slice index (Proof.Argon2.FillStep.random p pass lane slice index rightState.memory) := by
  cases mode : independent p pass slice
  · exact h.references mode
  · simp only [Proof.Argon2.FillStep.random, mode, ite_true]

theorem source_public_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice index old leftState rightState)
      Impl.Argon2.AArch64.RandomSource.code (FillKernel.Related p pass lane slice index) := by
  intro s t ta tb a b hp ea eb
  obtain ⟨traces, _⟩ := RandomSource.code_rel p pass lane slice index old _ _ _ _ _ _ hp.source ea eb
  obtain ⟨_, a', runA, ha⟩ := RandomSource.code_ok s p pass lane slice index old hp.source.left leftState hp.leftMatrix
  obtain ⟨_, b', runB, hb⟩ := RandomSource.code_ok t p pass lane slice index old hp.source.right rightState hp.rightMatrix
  obtain ⟨_, sameA⟩ := Exec.det ea runA
  obtain ⟨_, sameB⟩ := Exec.det eb runB
  subst a'; subst b'
  refine ⟨traces, ?_⟩
  obtain ⟨_, readyA⟩ := ha.ready
  obtain ⟨_, readyB⟩ := hb.ready
  refine ⟨readyA.filling, readyB.filling, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (hp.source.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm)
  · exact ha.sp.trans
      (hp.source.stacks.trans hb.sp.symm)
  · exact (ha.frame_word hp.source.left 232 (by decide) (by decide)).trans
      (hp.source.matrices.trans (hb.frame_word hp.source.right 232 (by decide) (by decide)).symm)
  · exact (ha.frame_word hp.source.left 248 (by decide) (by decide)).trans
      (hp.source.work.trans (hb.frame_word hp.source.right 248 (by decide) (by decide)).symm)
  · rw [ha.random, hb.random]; exact hp.reference_eq

theorem code_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice index old leftState rightState)
      Impl.Argon2.AArch64.FillBlock.code (fun s t => s.sp = t.sp) :=
  (source_public_rel p pass lane slice index old leftState rightState).seq
    (FillKernel.code_rel p pass lane slice index)

end VG.Proof.Argon2.AArch64.FillBlock

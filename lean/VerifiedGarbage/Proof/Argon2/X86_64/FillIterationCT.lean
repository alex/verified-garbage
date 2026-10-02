import VerifiedGarbage.Proof.Argon2.X86_64.FillIteration
import VerifiedGarbage.Proof.Argon2.X86_64.FillSlicesCT

/-! Pass setup retains public pointers and exposes only the reviewed pass log. -/

namespace VG.Proof.Argon2.X86_64.FillIteration

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  left : Ready p pass s
  right : Ready p pass t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (fillPass p leftState pass).indices = (fillPass p rightState pass).indices

theorem setup_trace : RelCT isa (fun _ _ : State => True) (.block Impl.Argon2.X86_64.FillIteration.setup) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

theorem setup_public_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass leftState rightState) (.block Impl.Argon2.X86_64.FillIteration.setup)
      (fun s t => FillSlices.NextRelated p pass 0 leftState rightState s t ∧
        (fillPass p leftState pass).indices = (fillPass p rightState pass).indices) := by
  have trace := setup_trace.mono (P' := Related p pass leftState rightState)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨setup_ok s p pass h.left, setup_ok t p pass h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ?_, ?_, ?_, ?_⟩, hp.indices⟩
  · rw [ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]; exact hp.bases
  · rw [ha.keeps.regs .rsp (by decide), hb.keeps.regs .rsp (by decide)]; exact hp.stacks
  · unfold FillKernel.matrix
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]; exact hp.matrices
  · unfold AddressCalls.work
    rw [ha.keeps.mem, hb.keeps.mem, ha.keeps.regs .rbp (by decide), hb.keeps.regs .rbp (by decide)]; exact hp.work
  · unfold FillKernel.matrix; rw [ha.keeps.mem, ha.keeps.regs .rbp (by decide)]; exact hp.leftMatrix
  · unfold FillKernel.matrix; rw [hb.keeps.mem, hb.keeps.regs .rbp (by decide)]; exact hp.rightMatrix

theorem code_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass leftState rightState) Impl.Argon2.X86_64.FillIteration.code (fun _ _ => True) :=
  (setup_public_rel p pass leftState rightState).seq (FillSlices.pass_rel p pass leftState rightState)

end VG.Proof.Argon2.X86_64.FillIteration

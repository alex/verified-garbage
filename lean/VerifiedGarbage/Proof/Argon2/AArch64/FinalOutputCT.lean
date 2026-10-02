import VerifiedGarbage.Proof.Argon2.AArch64.FinalOutputReady
import VerifiedGarbage.Proof.Argon2.AArch64.FinalCallCT

/-! Final hashing exposes only the public tag length and pointers, for any hash backend. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : ReductionState.matrix s = ReductionState.matrix t
  outputs : output s = output t
  works : work s = work t

structure NextRelated (p : Params) (s t : State) : Prop where
  left : FinalCall.CallReady p.tagLen s
  right : FinalCall.CallReady p.tagLen t
  leftInputLength : s.gpr .x1 = 1024
  rightInputLength : t.gpr .x1 = 1024
  leftOutputLength : s.gpr .x3 = BitVec.ofNat 64 p.tagLen
  rightOutputLength : t.gpr .x3 = BitVec.ofNat 64 p.tagLen
  inputs : s.gpr .x0 = t.gpr .x0
  outputs : s.gpr .x2 = t.gpr .x2
  works : s.gpr .x4 = t.gpr .x4
  stacks : s.sp = t.sp

theorem args_trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.FinalOutput.args) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem args_rel (p : Params) : RelCT isa (Related p)
    (.block Impl.Argon2.AArch64.FinalOutput.args) (NextRelated p) := by
  have trace := args_trace.mono (P' := Related p) (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨args_ok s h.left.reads, args_ok t h.right.reads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready hp.left, hb.ready hp.right, ha.inputLength, hb.inputLength,
    ha.outputLength.trans hp.left.tagWord, hb.outputLength.trans hp.right.tagWord,
    ha.input.trans (hp.matrices.trans hb.input.symm), ha.output.trans (hp.outputs.trans hb.output.symm),
    ha.work.trans (hp.works.trans hb.work.symm),
    (ha.keeps.sp).trans (hp.stacks.trans (hb.keeps.sp).symm)⟩

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.AArch64.FinalOutput.code name v.hash) (fun _ _ => True) :=
  (args_rel p).seq (FinalCall.hPrime_call_rel v name p.tagLen (fun _ _ h =>
    ⟨h.left, h.right, h.leftInputLength, h.rightInputLength, h.leftOutputLength, h.rightOutputLength,
      h.inputs, h.outputs, h.works, h.stacks⟩))

end VG.Proof.Argon2.AArch64.FinalOutput

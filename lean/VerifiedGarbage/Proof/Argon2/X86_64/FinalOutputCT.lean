import VerifiedGarbage.Proof.Argon2.X86_64.FinalOutputReady
import VerifiedGarbage.Proof.Argon2.X86_64.FinalCallCT

/-! Final hashing exposes only the public tag length and pointers, for any hash backend. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : ReductionState.matrix s = ReductionState.matrix t
  outputs : output s = output t
  works : work s = work t

structure NextRelated (p : Params) (s t : State) : Prop where
  left : FinalCall.CallReady p.tagLen s
  right : FinalCall.CallReady p.tagLen t
  leftInputLength : s.gpr .rsi = 1024
  rightInputLength : t.gpr .rsi = 1024
  leftOutputLength : s.gpr .rcx = BitVec.ofNat 64 p.tagLen
  rightOutputLength : t.gpr .rcx = BitVec.ofNat 64 p.tagLen
  inputs : s.gpr .rdi = t.gpr .rdi
  outputs : s.gpr .rdx = t.gpr .rdx
  works : s.gpr .r8 = t.gpr .r8
  stacks : s.gpr .rsp = t.gpr .rsp

theorem args_trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.FinalOutput.args) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem args_rel (p : Params) : RelCT isa (Related p)
    (.block Impl.Argon2.X86_64.FinalOutput.args) (NextRelated p) := by
  have trace := args_trace.mono (P' := Related p) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨args_ok s h.left.reads, args_ok t h.right.reads⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready hp.left, hb.ready hp.right, ha.inputLength, hb.inputLength,
    ha.outputLength.trans hp.left.tagWord, hb.outputLength.trans hp.right.tagWord,
    ha.input.trans (hp.matrices.trans hb.input.symm), ha.output.trans (hp.outputs.trans hb.output.symm),
    ha.work.trans (hp.works.trans hb.work.symm),
    (ha.regs .rsp (by simp [calleeSaved])).trans (hp.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm)⟩

theorem code_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.X86_64.FinalOutput.code name (HPrime.hash v)) (fun _ _ => True) :=
  (args_rel p).seq (FinalCall.hPrime_call_rel v name p.tagLen (fun _ _ h =>
    ⟨h.left, h.right, h.leftInputLength, h.rightInputLength, h.leftOutputLength, h.rightOutputLength,
      h.inputs, h.outputs, h.works, h.stacks⟩))

end VG.Proof.Argon2.X86_64.FinalOutput

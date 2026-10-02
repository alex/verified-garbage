import VerifiedGarbage.Proof.Argon2.X86_64.AddressCalls
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressCallCT

/-! The two address-generation compression calls have public fixed addresses. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCalls

structure Related (s t : State) : Prop where
  left : Ready s
  right : Ready t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  work : work s = work t

structure CallRelated (s t : State) : Prop where
  left : FillCompress.CallReady s
  right : FillCompress.CallReady t
  args : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s.gpr r = t.gpr r

theorem first_args_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block (args 7168 5120 4096)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem second_args_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block (args 7168 4096 6144)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem args_public_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (args x y out)) (fun _ _ => True)) :
    RelCT isa Related (.block (args x y out)) CallRelated := by
  have trace := argTrace.mono (P' := Related) (fun _ _ hp => hp.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨args_nat_ok s hp.left x y out (by omega) (by omega) (by omega),
      args_nat_ok t hp.right x y out (by omega) (by omega) (by omega)⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨args_call_ready s a hp.left x y out hx hy ho bx by_ bo ha,
    args_call_ready t b hp.right x y out hx hy ho bx by_ bo hb, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha.left.trans ((congrArg (fun p => off p x) hp.work).trans hb.left.symm)
  · exact ha.right.trans ((congrArg (fun p => off p y) hp.work).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (fun p => off p out) hp.work).trans hb.output.symm)
  · exact ha.scratch.trans (hp.work.trans hb.scratch.symm)
  · exact (ha.keeps.regs .rsp (by decide)).trans
      (hp.stacks.trans (hb.keeps.regs .rsp (by decide)).symm)

theorem stage_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (args x y out)) (fun _ _ => True)) :
    RelCT isa Related (stage x y out) Related := by
  have call := FillCompress.call_rel Spec.Argon2.compressApi.name (P := CallRelated)
    (fun _ _ hp => ⟨hp.left, hp.right, hp.args .rdi (by simp), hp.args .rsi (by simp),
      hp.args .rdx (by simp), hp.args .rcx (by simp), hp.args .rsp (by simp)⟩)
  have trace := (args_public_rel x y out hx hy ho bx by_ bo argTrace).seq call
  have full := trace.wpDep (fun s t hp =>
    ⟨stage_ok s hp.left x y out hx hy ho bx by_ bo,
      stage_ok t hp.right x y out hx hy ho bx by_ bo⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready, hb.ready,
    (ha.regs .rbp (by simp [calleeSaved])).trans
      (hp.bases.trans (hb.regs .rbp (by simp [calleeSaved])).symm),
    (ha.regs .rsp (by simp [calleeSaved])).trans
      (hp.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩

theorem calls_rel : RelCT isa Related calls Related :=
  (stage_rel 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) first_args_rel).seq
  (stage_rel 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) second_args_rel)

end VG.Proof.Argon2.X86_64.AddressCalls

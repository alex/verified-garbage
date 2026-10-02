import VerifiedGarbage.Proof.Argon2.AArch64.AddressCalls
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCallCT

/-! The two address-generation compression calls have public fixed addresses. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCalls

structure Related (s t : State) : Prop where
  left : Ready s
  right : Ready t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  work : work s = work t

structure CallRelated (s t : State) : Prop where
  left : FillCompress.CallReady s
  right : FillCompress.CallReady t
  stacks : s.sp = t.sp
  args : ∀ r ∈ [Reg.x0, .x1, .x2, .x3], s.gpr r = t.gpr r

theorem first_args_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (args 7168 5120 4096)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem second_args_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block (args 7168 4096 6144)) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem args_public_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (args x y out)) (fun s t => s.sp = t.sp)) :
    RelCT isa Related (.block (args x y out)) CallRelated := by
  have trace := argTrace.mono (P' := Related) (fun _ _ hp => ⟨hp.bases, hp.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨args_nat_ok s hp.left x y out (by omega) (by omega) (by omega),
      args_nat_ok t hp.right x y out (by omega) (by omega) (by omega)⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  refine ⟨args_call_ready s a hp.left x y out hx hy ho bx by_ bo ha,
    args_call_ready t b hp.right x y out hx hy ho bx by_ bo hb, eq, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ha.left.trans ((congrArg (fun p => off p x) hp.work).trans hb.left.symm)
  · exact ha.right.trans ((congrArg (fun p => off p y) hp.work).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (fun p => off p out) hp.work).trans hb.output.symm)
  · exact ha.scratch.trans (hp.work.trans hb.scratch.symm)

theorem stage_rel (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (argTrace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
      (.block (args x y out)) (fun s t => s.sp = t.sp)) :
    RelCT isa Related (stage x y out) Related := by
  have call := FillCompress.call_rel Spec.Argon2.compressApi.name (P := CallRelated)
    (fun _ _ hp => ⟨hp.left, hp.right, hp.args .x0 (by simp), hp.args .x1 (by simp),
      hp.args .x2 (by simp), hp.args .x3 (by simp), hp.stacks⟩)
  have trace := (args_public_rel x y out hx hy ho bx by_ bo argTrace).seq call
  have full := trace.wpDep (fun s t hp =>
    ⟨stage_ok s hp.left x y out hx hy ho bx by_ bo,
      stage_ok t hp.right x y out hx hy ho bx by_ bo⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact ⟨ha.ready, hb.ready,
    (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (hp.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm),
    ha.sp.trans (hp.stacks.trans hb.sp.symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩

theorem calls_rel : RelCT isa Related calls Related :=
  (stage_rel 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) first_args_rel).seq
  (stage_rel 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) second_args_rel)

end VG.Proof.Argon2.AArch64.AddressCalls

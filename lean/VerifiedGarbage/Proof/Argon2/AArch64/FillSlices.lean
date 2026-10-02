import VerifiedGarbage.Proof.Argon2.AArch64.FillSlicesBody
import VerifiedGarbage.Proof.Argon2.Slices

/-! Termination and correctness of the four-slice filling pass. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {pass slice : Nat} {state : FillState}
    (h : Done s t p pass slice state) (last : slice + 1 = 4) :
    Finished s t p pass (Proof.Argon2.lanes p pass slice 0 p.lanes state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.sp, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass slice : Nat} {state finalState : FillState}
    (first : Done s a p pass slice state) (rest : Finished a t p pass finalState) : Finished s t p pass finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_⟩
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass slice : Nat)
    (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    WP isa Impl.Argon2.AArch64.FillSlices.loop s (Finished s · p pass (Proof.Argon2.slices p pass slice count state)) := by
  induction count generalizing s slice state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass slice h state represented
    rw [Proof.Argon2.slices_succ]
    cases n with
    | zero =>
      have last : slice + 1 = 4 := endSlice
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : slice + 1 < 4 := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (slice + 1) (done.next active)
        (Proof.Argon2.lanes p pass slice 0 p.lanes state) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

theorem pass_ok (s : State) (p : Params) (pass : Nat) (h : FillSlice.Ready p pass 0 s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlices.loop s (Finished s · p pass (fillPass p state pass)) := by
  rw [← Proof.Argon2.slices_pass p pass state]
  exact loop_ok 4 s p pass 0 h state represented (by decide) (by decide)

end VG.Proof.Argon2.AArch64.FillSlices

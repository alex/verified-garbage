import VerifiedGarbage.Proof.Argon2.X86_64.FillLanesBody
import VerifiedGarbage.Proof.Argon2.Lanes

/-! Termination and correctness of all remaining lanes in one slice. -/

namespace VG.Proof.Argon2.X86_64.FillLanes

open VG VG.X86_64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r15 → t.gpr r = s.gpr r
  header : ∃ lane a, lane + 1 = p.lanes ∧ SegmentSetup.Ready p pass lane slice a ∧ Divide.Keeps [.rbx] a t

theorem Done.finished {s t : State} {p : Params} {pass lane slice : Nat} {state : FillState}
    (h : Done s t p pass lane slice state) (last : lane + 1 = p.lanes) :
    Finished s t p pass slice (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) := by
  obtain ⟨a, ready, keeps⟩ := h.header
  exact ⟨h.represented, h.matrix, h.work, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.mxcsr,
    h.regs, lane, a, last, ready, keeps⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass lane slice : Nat} {state finalState : FillState}
    (first : Done s a p pass lane slice state) (rest : Finished a t p pass slice finalState) :
    Finished s t p pass slice finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_, rest.header⟩
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.regs .rsp (by simp [calleeSaved]) (by decide) (by decide),
      first.regs .rbp (by simp [calleeSaved]) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx ix; exact (rest.regs r hr bx ix).trans (first.regs r hr bx ix)

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass lane slice : Nat)
    (h : SegmentSetup.Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.X86_64.FillLanes.loop s
      (Finished s · p pass slice (Proof.Argon2.lanes p pass slice lane count state)) := by
  induction count generalizing s lane state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass lane slice h state represented
    rw [Proof.Argon2.lanes_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active)
        (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

end VG.Proof.Argon2.X86_64.FillLanes

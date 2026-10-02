import VerifiedGarbage.Proof.Argon2.X86_64.ReduceLanesBody


/-! Termination and correctness of the final lane reduction. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Finished (s t : State) (p : Params) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc : Block}
    (h : Done s t p lane memory acc) (last : lane + 1 = p.lanes) : Finished s t p memory acc :=
  ⟨h.represented, h.base, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.mxcsr, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc result : Block}
    (first : Done s a p lane memory acc) (rest : Finished a t p memory result) : Finished s t p memory result := by
  refine ⟨rest.represented, rest.base.trans first.base, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_⟩
  · have frame := rest.frame
    rw [first.base] at frame
    exact first.frame.trans frame
  · intro r hr bx; exact (rest.regs r hr bx).trans (first.regs r hr bx)

theorem loop_ok (count : Nat) (s : State) (p : Params) (lane : Nat) (h : Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.X86_64.ReduceLanes.loop s
      (Finished s · p memory (Proof.Argon2.reduction p memory lane count acc)) := by
  induction count generalizing s lane acc with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p lane h memory acc represented
    rw [Proof.Argon2.reduction_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active) _
        done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

end VG.Proof.Argon2.X86_64.ReduceLanes

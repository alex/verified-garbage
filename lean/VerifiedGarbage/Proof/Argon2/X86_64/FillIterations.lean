import VerifiedGarbage.Proof.Argon2.X86_64.FillIterationsBody
import VerifiedGarbage.Proof.Argon2.Iterations

/-! Termination and correctness of every requested filling pass. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p p.passes p.lanes 4 t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {pass : Nat} {state : FillState}
    (h : Done s t p pass state) (last : pass + 1 = p.passes) : Finished s t p (fillPass p state pass) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.header, h.rd, h.wr, h.frame, h.mxcsr, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass : Nat} {state finalState : FillState}
    (first : Done s a p pass state) (rest : Finished a t p finalState) : Finished s t p finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work, rest.header,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_⟩
  · have frame := rest.frame
    rw [writes, first.matrix, first.work,
      first.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide),
      first.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at frame
    exact first.frame.trans frame
  · intro r hr bx sl ix; exact (rest.regs r hr bx sl ix).trans (first.regs r hr bx sl ix)

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    WP isa Impl.Argon2.X86_64.FillIterations.loop s (Finished s · p (Proof.Argon2.iterations p pass count state)) := by
  induction count generalizing s pass state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass h state represented
    rw [Proof.Argon2.iterations_succ]
    cases n with
    | zero =>
      have last : pass + 1 = p.passes := endPass
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : pass + 1 < p.passes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (pass + 1) (done.next active)
        (fillPass p state pass) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

theorem Finished.frame_word {s t : State} {p : Params} {pass : Nat} {state : FillState}
    (ready : Ready p pass s) (done : Finished s t p state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : 24 ≤ d) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)]
  obtain ⟨lane, slice, header⟩ := ready.filling.header
  have sub : Region.Sub ⟨off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact header.layout.matrixFrame.symm.sub_left sub
    · exact header.addressLayout.frameWork.sub_left sub
    · exact header.addressLayout.frameStack.sub_left sub
    · simpa only [off, BitVec.add_zero] using Offset.disjoint (d := d) (n := 8) (e := 0) (k := 24) (s.gpr .rbp) (Or.inr (by omega)) (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.FillIterations

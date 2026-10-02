import VerifiedGarbage.Proof.Argon2.AArch64.FillSegmentBody
import VerifiedGarbage.Proof.Argon2.Segment

/-! Termination and correctness of the active suffix of one segment. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass lane slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice p.segmentLen t
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp

theorem Done.finished {s t : State} {p : Params} {pass lane slice index : Nat} {state : FillState}
    (h : Done s t p pass lane slice index state) (last : index + 1 = p.segmentLen) :
    Finished s t p pass lane slice (fillBlock p pass slice lane index state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.position, h.layout, h.cache,
    h.matrixWork, h.passWord, h.lanesWord, h.regs, h.rd, h.wr, h.frame, h.sp⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass lane slice index : Nat}
    {state finalState : FillState} (first : Done s a p pass lane slice index state)
    (rest : Finished a t p pass lane slice finalState) : Finished s t p pass lane slice finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work,
    rest.position, rest.layout, rest.cache, rest.matrixWork, rest.passWord, rest.lanesWord,
    ?_, rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp⟩
  · intro r hr ne; exact (rest.regs r hr ne).trans (first.regs r hr ne)
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.sp,
      first.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)] at frame
    exact first.frame.trans frame

theorem loop_ok (count : Nat) (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endIndex : index + count = p.segmentLen) :
    WP isa Impl.Argon2.AArch64.FillSegment.loop s
      (Finished s · p pass lane slice (Proof.Argon2.segment p pass lane slice index count state)) := by
  induction count generalizing s index old state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p pass lane slice index old h state represented
    rw [Proof.Argon2.segment_succ]
    cases n with
    | zero =>
      have last : index + 1 = p.segmentLen := endIndex
      refine ⟨_, a, .loopExit run ?_, ?_⟩
      · simp only [done.cf, last, Nat.lt_irrefl, decide_false]
      · exact done.finished last
    | succ n =>
      have active : index + 1 < p.segmentLen := by omega
      obtain ⟨nextCounter, nextReady⟩ := done.next active
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (index + 1) nextCounter nextReady
        (fillBlock p pass slice lane index state) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

end VG.Proof.Argon2.AArch64.FillSegment

import VerifiedGarbage.Proof.Argon2.X86_64.FillIndex
import VerifiedGarbage.Proof.Argon2.X86_64.FillAllocation

/-! One segment iteration updates the specified cell and advances its public index. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice (index + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .r15 → t.gpr r = s.gpr r
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes
  cf : t.cf = decide (index + 1 < p.segmentLen)
  next : index + 1 < p.segmentLen → ∃ old, RandomSource.Ready p pass lane slice (index + 1) old t

theorem body_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillSegment.body s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.X86_64.FillSegment.body
  refine WP.seq ((FillBlock.code_ok s p pass lane slice index old h state represented).mono ?_)
  intro a filled
  obtain ⟨counter, ready⟩ := filled.ready
  refine (advance_nat_ok a p pass lane slice index ready.filling).mono ?_
  rintro t ⟨value, cf, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, ?_, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.mxcsr.trans filled.mxcsr, ?_, ?_, ?_, ?_, ?_, ?_, cf, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · exact ⟨(keeps.regs .rbx (by decide)).trans ready.filling.position.current,
      (keeps.regs .r12 (by decide)).trans ready.filling.position.laneLength,
      (keeps.regs .r13 (by decide)).trans ready.filling.position.segmentLength,
      (keeps.regs .r14 (by decide)).trans ready.filling.position.slice, value⟩
  · rw [keeps.mem]; exact filled.frame
  · intro r hr ne
    have outside : r ∉ [Reg.r15] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ne
    exact (keeps.regs r outside).trans (filled.regs r hr)
  · exact ready.filling.layout.of_preserved bp (keeps.regs .rsp (by decide)) base work keeps.rd keeps.wr
  · exact ⟨counter, ready.cache.of_state (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr⟩
  · rw [base, work]; exact ready.matrixWork
  · rw [keeps.mem, bp]; exact ready.filling.passWord
  · rw [keeps.mem, bp]; exact ready.filling.lanesWord
  · intro active; exact ⟨counter, next_ready ready keeps value active⟩

end VG.Proof.Argon2.X86_64.FillSegment

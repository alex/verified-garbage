import VerifiedGarbage.Impl.Argon2.X86_64.FillSlices
import VerifiedGarbage.Proof.Argon2.X86_64.FillSlice

/-! Merged from `Proof.Argon2.X86_64.FillSliceAdvance`. -/
section
/-! Slice advancement retains the public header and matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSlices

theorem advance_ok (s : State) : WP isa (.block advance) s fun t =>
    t.gpr .r14 = s.gpr .r14 + 1 ∧ t.cf = decide ((s.gpr .r14 + 1).toNat < 4) ∧ Divide.Keeps [.r14] s t := by
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (4 : BitVec 32) = (4 : Addr) from rfl,
    show (4 : Addr).toNat = 4 from rfl,
    ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem advanced_header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : FillHeader.Ready p pass lane slice s) (k : Divide.Keeps [.r14] s t)
    (value : t.gpr .r14 = BitVec.ofNat 64 (slice + 1)) : FillHeader.Ready p pass lane (slice + 1) t := by
  obtain ⟨old, words⟩ := h.words
  exact h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k.regs _ (by decide))
    k.mem k.rd k.wr ((k.regs .rbx (by decide)).trans words.laneWord) value

end VG.Proof.Argon2.X86_64.FillSlices
end

/-! Fill one slice and advance its public coordinate. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.lanes p pass slice 0 p.lanes state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes (slice + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  cf : t.cf = decide (slice + 1 < 4)
  next : slice + 1 < 4 → FillSlice.Ready p pass (slice + 1) t

theorem body_ok (s : State) (p : Params) (pass slice : Nat) (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillSlices.body s (Done s · p pass slice state) := by
  unfold Impl.Argon2.X86_64.FillSlices.body
  refine WP.seq ((FillSlice.code_ok s p pass slice h state represented).mono ?_)
  intro a filled
  have header := FillHeader.of_lanes_finished filled
  obtain ⟨old, words⟩ := header.words
  refine (advance_ok a).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have added : a.gpr .r14 + 1 = BitVec.ofNat 64 (slice + 1) := by
    rw [words.sliceWord, BitVec.ofNat_add]; rfl
  have nextWord := value.trans added
  have nextHeader := advanced_header header keeps nextWord
  have bp := keeps.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  have sliceBound := h.parameters.sliceBound
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextHeader, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.mxcsr.trans filled.mxcsr, ?_, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx sl ix
    have outside : r ∉ [Reg.r14] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sl
    exact (keeps.regs r outside).trans (filled.regs r hr bx ix)
  · rw [flag, added, ReferenceMap.word_nat (slice + 1) (by omega)]
  · intro active
    exact ⟨{ h.parameters with sliceBound := active }, p.lanes, nextHeader⟩

end VG.Proof.Argon2.X86_64.FillSlices

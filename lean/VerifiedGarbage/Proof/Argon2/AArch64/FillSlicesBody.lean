import VerifiedGarbage.Proof.Argon2.AArch64.FillSliceAdvance

/-! Fill one slice and advance its public coordinate. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (Proof.Argon2.lanes p pass slice 0 p.lanes state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  header : FillHeader.Ready p pass p.lanes (slice + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  cf : eval (.nonzero .x .x14) t = some (decide (slice + 1 < 4))
  next : slice + 1 < 4 → FillSlice.Ready p pass (slice + 1) t

theorem body_ok (s : State) (p : Params) (pass slice : Nat) (h : FillSlice.Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlices.body s (Done s · p pass slice state) := by
  unfold Impl.Argon2.AArch64.FillSlices.body
  refine WP.seq ((FillSlice.code_ok s p pass slice h state represented).mono ?_)
  intro a filled
  have header := FillHeader.of_lanes_finished filled
  obtain ⟨old, words⟩ := header.words
  have sliceBound := h.parameters.sliceBound
  have added : a.gpr .x22 + 1 = BitVec.ofNat 64 (slice + 1) := by
    rw [words.sliceWord, BitVec.ofNat_add]; rfl
  have inputBound : (a.gpr .x22 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (slice + 1) (by omega)]; omega
  refine (advance_ok a inputBound).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have nextWord := value.trans added
  have nextHeader := advanced_header header keeps nextWord
  have bp := keeps.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, nextHeader, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.sp.trans filled.sp, ?_, ?_, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · rw [keeps.mem]; exact filled.frame
  · intro r hr bx sl ix
    have outside : r ∉ [Reg.x22, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (filled.regs r hr bx ix)
  · rw [flag, added, ReferenceMap.word_nat (slice + 1) (by omega)]
  · intro active
    exact ⟨{ h.parameters with sliceBound := active }, p.lanes, nextHeader⟩

end VG.Proof.Argon2.AArch64.FillSlices

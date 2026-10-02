import VerifiedGarbage.Impl.Argon2.AArch64.FillSegment
import VerifiedGarbage.Proof.Argon2.AArch64.FillBlock

/-! Public segment-index advancement retains the filling and cache allocations. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSegment

theorem advance_ok (s : State)
    (ha : (s.gpr .x23 + 1).toNat < 2 ^ 63) (hb : (s.gpr .x21).toNat < 2 ^ 63) :
    WP isa (.block advance) s fun t =>
      t.gpr .x23 = s.gpr .x23 + 1 ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x23 + 1).toNat < (s.gpr .x21).toNat)) ∧
      Divide.Keeps [.x23, .x12, .x14, .x15] s t := by
  simp only [advance, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.addi_ok s .x23 1 (by decide) (by decide) (by decide)).mono ?_
  rintro a ⟨value, ka⟩
  have endEq := ka.regs .x21 (by decide)
  refine (Instructions.compare_ok a .x23 .x21 (by rw [value]; exact ha)
    (by rw [endEq]; exact hb)).mono ?_
  rintro t ⟨flag, kt⟩
  refine ⟨(kt.regs .x23 (by decide)).trans value, ?_, ?_⟩
  · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, value, endEq]
    cases decide ((s.gpr .x23 + 1).toNat < (s.gpr .x21).toNat) <;> rfl
  · exact (ka.mono (by decide)).trans (kt.mono (by decide))

theorem advance_nat_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa (.block advance) s fun t =>
      t.gpr .x23 = BitVec.ofNat 64 (index + 1) ∧
      eval (.nonzero .x .x14) t = some (decide (index + 1 < p.segmentLen)) ∧ Divide.Keeps [.x23, .x12, .x14, .x15] s t := by
  have inputBound : (s.gpr .x23 + 1).toNat < 2 ^ 63 := by
    rw [h.position.index, show (1 : Addr) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add,
      ReferenceMap.word_nat (index + 1) (by
        have := h.bounds.indexBound
        have := h.bounds.segment_le_lane
        have := h.bounds.laneLength_bound
        omega)]
    have := h.bounds.indexBound
    have := h.bounds.segment_le_lane
    have := h.bounds.laneLength_bound
    omega
  have endBound63 : (s.gpr .x21).toNat < 2 ^ 63 := by
    rw [h.position.segmentLength, ReferenceMap.word_nat p.segmentLen
      (Nat.lt_of_le_of_lt h.bounds.segment_le_lane
        (Nat.lt_trans h.bounds.laneLength_bound (by decide)))]
    have := h.bounds.segment_le_lane
    have := h.bounds.laneLength_bound
    omega
  refine (advance_ok s inputBound endBound63).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have added : s.gpr .x23 + 1 = BitVec.ofNat 64 (index + 1) := by
    rw [h.position.index, BitVec.ofNat_add]; rfl
  have endBound : p.segmentLen < 2 ^ 64 := Nat.lt_of_le_of_lt h.bounds.segment_le_lane
    (Nat.lt_trans h.bounds.laneLength_bound (by decide))
  have indexBound := h.bounds.indexBound
  refine ⟨value.trans added, ?_, keeps⟩
  rw [flag, added, h.position.segmentLength,
    ReferenceMap.word_nat (index + 1) (by omega), ReferenceMap.word_nat p.segmentLen endBound]

theorem next_ready {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : RandomSource.Ready p pass lane slice index old s)
    (k : Divide.Keeps [.x23, .x12, .x14, .x15] s t) (value : t.gpr .x23 = BitVec.ofNat 64 (index + 1))
    (active : index + 1 < p.segmentLen) : RandomSource.Ready p pass lane slice (index + 1) old t := by
  have bp := k.regs .x19 (by decide)
  have sp := k.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  have kernelWork : FillKernel.work t = FillKernel.work s := work
  refine ⟨?_, h.cache.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact k.regs _ (by decide)) k.sp k.mem k.rd k.wr, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · rw [k.rd, k.wr, bp]; exact h.filling.layout.frameRead
      · rw [k.wr, bp]; exact h.filling.layout.frameWrite
      · rw [base, k.wr]; exact h.filling.layout.matrixWrite
      · rw [kernelWork, k.wr]; exact h.filling.layout.workWrite
      · rw [base, kernelWork]; exact h.filling.layout.matrixWork
      · rw [base, bp]; exact h.filling.layout.matrixFrame
      · rw [base, sp]; exact h.filling.layout.matrixStack
      · rw [bp, kernelWork]; exact h.filling.layout.frameWork
      · rw [bp, sp]; exact h.filling.layout.frameStack
      · rw [sp, kernelWork]; exact h.filling.layout.stackWork
    · have bounds := h.filling.bounds
      refine ⟨bounds.lanesPositive, bounds.lanesBound, bounds.memoryMinimum, bounds.memoryBound,
        bounds.passBound, bounds.laneBound, bounds.sliceBound, active, ?_⟩
      rcases bounds.active with hp | hs | hi
      · exact Or.inl hp
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr (by omega))
    · exact ⟨(k.regs .x24 (by decide)).trans h.filling.position.current,
        (k.regs .x20 (by decide)).trans h.filling.position.laneLength,
        (k.regs .x21 (by decide)).trans h.filling.position.segmentLength,
        (k.regs .x22 (by decide)).trans h.filling.position.slice, value⟩
    · rw [k.mem, bp]; exact h.filling.passWord
    · rw [k.mem, bp]; exact h.filling.lanesWord
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.AArch64.FillSegment

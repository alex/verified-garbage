import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelStable
import VerifiedGarbage.Impl.Argon2.AArch64.FillSegment
import VerifiedGarbage.Proof.Argon2.AArch64.FillBlock

/-! Merged from `Proof.Argon2.AArch64.FillIndex`. -/
section
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
end

/-! Merged from `Proof.Argon2.AArch64.FillAllocation`. -/
section
/-! Transport the allocation using just its public pointers and permissions. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem Layout.of_preserved {p : Params} {s t : State} (h : Layout p s)
    (bp : t.gpr .x19 = s.gpr .x19) (sp : t.sp = s.sp)
    (base : matrix t = matrix s) (scratch : work t = work s)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Layout p t := by
  constructor
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [wr, bp]; exact h.frameWrite
  · rw [base, wr]; exact h.matrixWrite
  · rw [scratch, wr]; exact h.workWrite
  · rw [base, scratch]; exact h.matrixWork
  · rw [base, bp]; exact h.matrixFrame
  · rw [base, sp]; exact h.matrixStack
  · rw [bp, scratch]; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, scratch]; exact h.stackWork

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! One segment iteration updates the specified cell and advances its public index. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice (index + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x23 → t.gpr r = s.gpr r
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes
  cf : eval (.nonzero .x .x14) t = some (decide (index + 1 < p.segmentLen))
  next : index + 1 < p.segmentLen → ∃ old, RandomSource.Ready p pass lane slice (index + 1) old t

theorem body_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSegment.body s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.AArch64.FillSegment.body
  refine WP.seq ((FillBlock.code_ok s p pass lane slice index old h state represented).mono ?_)
  intro a filled
  obtain ⟨counter, ready⟩ := filled.ready
  refine (advance_nat_ok a p pass lane slice index ready.filling).mono ?_
  rintro t ⟨value, cf, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, ?_, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, keeps.sp.trans filled.sp, ?_, ?_, ?_, ?_, ?_, ?_, cf, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · exact ⟨(keeps.regs .x24 (by decide)).trans ready.filling.position.current,
      (keeps.regs .x20 (by decide)).trans ready.filling.position.laneLength,
      (keeps.regs .x21 (by decide)).trans ready.filling.position.segmentLength,
      (keeps.regs .x22 (by decide)).trans ready.filling.position.slice, value⟩
  · rw [keeps.mem]; exact filled.frame
  · intro r hr ne
    have outside : r ∉ [Reg.x23, .x12, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (filled.regs r hr)
  · exact ready.filling.layout.of_preserved bp (keeps.sp) base work keeps.rd keeps.wr
  · exact ⟨counter, ready.cache.of_state (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr⟩
  · rw [base, work]; exact ready.matrixWork
  · rw [keeps.mem, bp]; exact ready.filling.passWord
  · rw [keeps.mem, bp]; exact ready.filling.lanesWord
  · intro active; exact ⟨counter, next_ready ready keeps value active⟩

end VG.Proof.Argon2.AArch64.FillSegment

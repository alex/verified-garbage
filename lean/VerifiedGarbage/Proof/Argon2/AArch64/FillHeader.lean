import VerifiedGarbage.Proof.Argon2.AArch64.FillLanes

/-! Allocation and normalized header across lane, slice and pass boundaries. -/

namespace VG.Proof.Argon2.AArch64.FillHeader

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass lane slice : Nat) (s : State) : Prop where
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  write : InRegions s.wr (off (s.gpr .x19) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .x20 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem of_segment_ready {p : Params} {pass lane slice : Nat} {s : State}
    (h : SegmentSetup.Ready p pass lane slice s) : Ready p pass lane slice s :=
  ⟨h.layout, h.addressLayout, h.reads, h.write, h.words, h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.segment {p : Params} {pass lane slice : Nat} {s : State}
    (h : Ready p pass lane slice s) (parameters : FillContext.Parameters p pass lane slice) :
    SegmentSetup.Ready p pass lane slice s :=
  ⟨parameters, h.layout, h.addressLayout, h.reads, h.write, h.words,
    h.matrixWork, h.laneLength, h.segmentLength, h.lanesWord⟩

theorem Ready.of_state {p : Params} {pass lane slice newLane newSlice : Nat} {s t : State}
    (h : Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.x19, .x20, .x21], t.gpr r = s.gpr r)
    (sp : t.sp = s.sp) (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (laneWord : t.gpr .x24 = BitVec.ofNat 64 newLane) (sliceWord : t.gpr .x22 = BitVec.ofNat 64 newSlice) :
    Ready p pass newLane newSlice t := by
  have bp := regs .x19 (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
    (regs .x20 (by simp)).trans h.laneLength, (regs .x21 (by simp)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, laneWord, sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [mem, bp]; exact h.lanesWord

theorem of_lanes_finished {p : Params} {pass slice : Nat} {s t : State} {state : FillState}
    (h : FillLanes.Finished s t p pass slice state) : Ready p pass p.lanes slice t := by
  obtain ⟨lane, a, _, ready, keeps⟩ := h.header
  obtain ⟨old, words⟩ := ready.words
  apply (of_segment_ready ready).of_state _ keeps.sp keeps.mem keeps.rd keeps.wr h.laneWord
    ((keeps.regs .x22 (by decide)).trans words.sliceWord)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide)

end VG.Proof.Argon2.AArch64.FillHeader

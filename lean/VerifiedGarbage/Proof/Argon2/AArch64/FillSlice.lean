import VerifiedGarbage.Impl.Argon2.AArch64.FillSlice
import VerifiedGarbage.Proof.Argon2.AArch64.FillLanes

/-! Merged from `Proof.Argon2.AArch64.FillSlicePrepare`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillHeader`. -/
section
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
end

/-! Initialize lane zero without requiring a valid incoming lane coordinate. -/

namespace VG.Proof.Argon2.AArch64.FillSlice

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 slice
  header : ∃ lane, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : Params) (pass slice : Nat) : Prop where
  ready : SegmentSetup.Ready p pass 0 slice t
  keeps : Divide.Keeps [.x24] s t

theorem setup_ok (s : State) (p : Params) (pass slice : Nat) (h : Ready p pass slice s) :
    WP isa (.block Impl.Argon2.AArch64.FillSlice.setup) s (Prepared s · p pass slice) := by
  refine (SegmentSetup.register_ok s .x24 0 (by decide)).mono ?_
  rintro t ⟨laneWord, keeps⟩
  obtain ⟨lane, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass 0 slice t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.sp keeps.mem keeps.rd keeps.wr laneWord ((keeps.regs .x22 (by decide)).trans words.sliceWord)
  exact ⟨next.segment h.parameters, keeps⟩

end VG.Proof.Argon2.AArch64.FillSlice
end

/-! Correctness of one complete slice, starting at lane zero. -/

namespace VG.Proof.Argon2.AArch64.FillSlice

open VG VG.AArch64 VG.Spec.Argon2

theorem code_ok (s : State) (p : Params) (pass slice : Nat) (h : Ready p pass slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillSlice.code s
      (FillLanes.Finished s · p pass slice (Proof.Argon2.lanes p pass slice 0 p.lanes state)) := by
  unfold Impl.Argon2.AArch64.FillSlice.code
  refine WP.seq ((setup_ok s p pass slice h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .x19 (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillLanes.loop_ok p.lanes a p pass 0 slice prepared.ready state representedA
    h.parameters.lanesPositive (by omega)).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.laneWord,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.sp.trans prepared.keeps.sp, ?_, finished.header⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.sp, bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx ix
    have ne : r ∉ [Reg.x24] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact bx
    exact (finished.regs r hr bx ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.AArch64.FillSlice

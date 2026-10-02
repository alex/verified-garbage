import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupSteps

/-! Segment setup needs no previously valid cached block. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass lane slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass lane slice
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  write : InRegions s.wr (off (s.gpr .x19) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .x20 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Ready.of_state {p : Params} {pass lane slice : Nat} {s t : State}
    (h : Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.x19, .x24, .x20, .x21, .x22], t.gpr r = s.gpr r)
    (sp : t.sp = s.sp) (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Ready p pass lane slice t := by
  have bp := regs .x19 (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
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
    refine ⟨old, ?_, (regs .x24 (by simp)).trans words.laneWord,
      (regs .x22 (by simp)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [mem, bp]; exact h.lanesWord

theorem Ready.saved {p : Params} {pass lane slice : Nat} {s t : State}
    (h : Ready p pass lane slice s) (saved : AddressCache.Saved s t) : Ready p pass lane slice t := by
  have bp := congrFun saved.regs Reg.x19
  have sp := saved.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := saved.read 232 (by decide) (by decide)
  refine ⟨h.parameters, h.layout.of_preserved bp sp base saved.work_eq saved.rd saved.wr,
    saved.ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [saved.rd, saved.wr, bp]; exact h.reads
  · rw [saved.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    exact ⟨(s.gpr .x8).toNat, saved.words words (by simp)⟩
  · rw [base, saved.work_eq]; exact h.matrixWork
  · rw [saved.regs]; exact h.laneLength
  · rw [saved.regs]; exact h.segmentLength
  · exact (saved.read 184 (by decide) (by decide)).trans h.lanesWord

end VG.Proof.Argon2.AArch64.SegmentSetup

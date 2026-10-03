import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupSteps

/-! Merged from `Proof.Argon2.AArch64.SegmentSetupReset`. -/
section
/-! Merged from `Proof.Argon2.AArch64.SegmentSetupReady`. -/
section
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
end

/-! Reset the counter while preserving the segment header and matrix allocation. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure Reset (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  ready : Ready p pass lane slice t
  words : AddressHeader.Words p pass lane slice 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (s.gpr .x19) 8, 8⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem reset_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa reset s (Reset s · p pass lane slice) := by
  unfold reset
  refine WP.seq ((register_ok s .x8 0 (by decide)).mono ?_)
  rintro a ⟨value, keeps⟩
  have next := h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr
  refine (AddressCache.save_ready a next.addressLayout next.write).mono ?_
  intro t saved
  obtain ⟨old, words⟩ := next.words
  have matrixA : FillKernel.matrix a = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
  have workA : AddressCalls.work a = AddressCalls.work s := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .x19 (by decide)]
  refine ⟨next.saved saved, saved.words words value,
    (saved.read 232 (by decide) (by decide)).trans matrixA, saved.work_eq.trans workA,
    ?_, saved.rd.trans keeps.rd, saved.wr.trans keeps.wr, ?_, saved.sp.trans keeps.sp⟩
  · intro r hr
    have ne : r ∉ [Reg.x8] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (congrFun saved.regs r).trans (keeps.regs r ne)
  · have frame := saved.frame
    rw [keeps.mem, keeps.regs .x19 (by decide)] at frame
    exact frame

end VG.Proof.Argon2.AArch64.SegmentSetup
end

/-! The prepared context covers ordinary and empty first-segment suffixes. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure Prepared (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  context : FillContext.Ready p pass lane slice (start pass slice) 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (s.gpr .x19) 8, 8⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem prepare_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa prepare s (Prepared s · p pass lane slice) := by
  unfold prepare
  refine WP.seq ((reset_ok s p pass lane slice h).mono ?_)
  intro a reset
  refine (index_ok a pass slice (reset.ready.reads 0 (by simp)) reset.words.passWord reset.words.sliceWord
    (Nat.lt_trans h.parameters.passBound (by decide))
    (Nat.lt_trans h.parameters.sliceBound (by decide))).mono ?_
  rintro t ⟨value, keeps⟩
  have core := reset.ready.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr
  have cacheA : AddressCache.Invariant p pass lane slice 0 a :=
    ⟨reset.ready.addressLayout, reset.ready.reads, reset.ready.write, reset.words, by decide, Or.inl rfl⟩
  have cache := cacheA.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.sp keeps.mem keeps.rd keeps.wr
  have base : FillKernel.matrix t = FillKernel.matrix a := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .x19 (by decide)]
  have work : AddressCalls.work t = AddressCalls.work a := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .x19 (by decide)]
  refine ⟨⟨core.parameters, core.layout, cache, core.matrixWork,
    ⟨cache.words.laneWord, core.laneLength, core.segmentLength, cache.words.sliceWord, value⟩, core.lanesWord⟩,
    base.trans reset.matrix, work.trans reset.work, ?_, keeps.rd.trans reset.rd,
    keeps.wr.trans reset.wr, ?_, keeps.sp.trans reset.sp⟩
  · intro r hr ne
    have outside : r ∉ [Reg.x3, .x23, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (reset.regs r hr)
  · rw [keeps.mem]; exact reset.frame

theorem Prepared.represents {p : Params} {pass lane slice : Nat} {s t : State}
    (ready : Ready p pass lane slice s) (h : Prepared s t p pass lane slice) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  rw [h.matrix]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame h.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (ready.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.AArch64.SegmentSetup

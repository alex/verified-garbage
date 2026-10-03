import VerifiedGarbage.Proof.Argon2.AArch64.AddressCallsClear
import VerifiedGarbage.Proof.Argon2.AArch64.AddressHeaderCorrect

/-! Prepare the independent-address input and zero block from arbitrary scratch. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

structure Stable (s t : State) : Prop where
  ready : Ready t
  work_eq : work t = work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨work s, 8192⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem Stable.trans {s a t : State} (h : Stable s a) (k : Stable a t) : Stable s t := by
  have hf := k.frame
  rw [h.work_eq] at hf
  exact ⟨k.ready, k.work_eq.trans h.work_eq, fun r hr => (k.regs r hr).trans (h.regs r hr),
    k.rd.trans h.rd, k.wr.trans h.wr, h.frame.trans hf, k.sp.trans h.sp⟩

theorem Cleared.stable {s t : State} {offset : Nat} (h : Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : Stable s t :=
  ⟨h.ready, h.work_eq, h.regs, h.rd, h.wr, h.full_frame bound, h.sp⟩

theorem stable_of_frame {s t : State} (h : Ready s)
    (regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (frame : Frame [⟨work s, 8192⟩] s.mem t.mem) (mx : t.sp = s.sp) : Stable s t := by
  have bp := regs .x19 (by simp [FillCompress.loopRegs])
  have sp := mx
  have work' : work t = work s := by
    unfold work
    rw [bp, frame_word h frame 248 (by decide)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, work', regs, rd, wr, frame, mx⟩
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [work', wr]; exact h.workWrite
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem Stable.reads {s t : State} (h : Stable s t)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (off (t.gpr .x19) d) 8 := by
  rw [h.rd, h.wr, h.regs .x19 (by simp [FillCompress.loopRegs])]
  exact reads

theorem Stable.words {s t : State} {p : Params} {pass lane slice counter : Nat} (ready : Ready s) (h : Stable s t)
    (words : AddressHeader.Words p pass lane slice counter s) :
    AddressHeader.Words p pass lane slice counter t := by
  have bp := h.regs .x19 (by simp [FillCompress.loopRegs])
  have read (d : Nat) (hd : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bp]; exact frame_word ready h.frame d hd
  exact ⟨(read 0 (by decide)).trans words.passWord,
    (h.regs .x24 (by simp [FillCompress.loopRegs])).trans words.laneWord,
    (h.regs .x22 (by simp [FillCompress.loopRegs])).trans words.sliceWord,
    (read 240 (by decide)).trans words.blocksWord,
    (read 72 (by decide)).trans words.passesWord,
    (read 112 (by decide)).trans words.variantWord,
    (read 8 (by decide)).trans words.counterWord⟩

theorem pointer_stable {s a : State} (h : Ready s)
    (k : Divide.Keeps [.x0, .x12, .x15] s a) : Stable s a := by
  apply stable_of_frame h _ k.rd k.wr _ k.sp
  · intro r hr
    apply k.regs
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem Stable.input {s t : State} (ready : Ready s) (h : Stable s t) :
    AddressHeader.input t = AddressHeader.input s := by
  have value (i : Nat) (hi : i < 7) : AddressHeader.value t i = AddressHeader.value s i := by
    unfold AddressHeader.value
    rw [h.regs .x24 (by simp [FillCompress.loopRegs]), h.regs .x22 (by simp [FillCompress.loopRegs]),
      h.regs .x19 (by simp [FillCompress.loopRegs]),
      frame_word ready h.frame (Impl.Argon2.AArch64.AddressHeader.frameOffset i)
        (AddressHeader.offset_bound i hi)]
  unfold AddressHeader.input
  rw [value 0 (by decide), value 1 (by decide), value 2 (by decide), value 3 (by decide),
    value 4 (by decide), value 5 (by decide), value 6 (by decide)]

structure PreparedInput (s t : State) : Prop where
  stable : Stable s t
  zero : blockAt t.mem (off (work s) 7168) = zeroBlock
  input : blockAt t.mem (off (work s) 5120) = AddressHeader.input s

structure Prepared (s t : State) (p : Params) (pass lane slice counter : Nat) : Prop where
  stable : Stable s t
  zero : blockAt t.mem (off (work s) 7168) = zeroBlock
  input : blockAt t.mem (off (work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter

theorem prepare_layout_ok (s : State) (h : Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    : WP isa prepare s (PreparedInput s) := by
  unfold prepare
  refine WP.seq ((clearAt_ok s h 5120 (by decide)).mono ?_)
  intro a inputClear
  refine WP.seq ((clearAt_ok a inputClear.ready 7168 (by decide)).mono ?_)
  intro b zeroClear
  have stableB := (inputClear.stable (by decide)).trans (zeroClear.stable (by decide))
  have inputZero : blockAt b.mem (off (work s) 5120) = zeroBlock := by
    have kept := FillCompress.block_frame zeroClear.frame (p := off (work s) 5120) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      rw [inputClear.work_eq]
      exact Offset.disjoint _ (by decide) (by decide) (by decide))
    exact kept.trans inputClear.block
  refine WP.seq ((pointer_ok b 5120 (by decide) zeroClear.ready.frameRead).mono ?_)
  rintro c ⟨dest, keeps⟩
  have stableC := stableB.trans (pointer_stable zeroClear.ready keeps)
  have dest' : c.gpr .x0 = off (work s) 5120 := by rw [dest, stableB.work_eq]
  have write : Covers [⟨c.gpr .x0, 1024⟩] c.wr := by
    rw [dest, keeps.wr]; exact work_cover b zeroClear.ready 5120 1024 (by decide)
  have sep : (⟨c.gpr .x19, 272⟩ : Region).Disjoint ⟨c.gpr .x0, 1024⟩ := by
    rw [dest', stableC.regs .x19 (by simp [FillCompress.loopRegs])]
    exact h.frameWork.sub_right (Offset.sub_base _ (by decide))
  have zero : blockAt c.mem (c.gpr .x0) = zeroBlock := by rw [dest', keeps.mem]; exact inputZero
  refine (AddressHeader.code_ok c (stableC.reads reads) write sep zero).mono ?_
  rintro t ⟨input, frame, tk, mx⟩
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = c.gpr r := by
    intro r hr
    apply tk.1 _ _ (by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have frame' : Frame [⟨work c, 8192⟩] c.mem t.mem := by
    apply frame.sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    refine ⟨⟨work c, 8192⟩, by simp, ?_⟩
    rw [dest', stableC.work_eq]
    exact Offset.sub_base _ (by decide)
  have stableT := stableC.trans (stable_of_frame stableC.ready regs tk.2.1 tk.2.2 frame' mx)
  refine ⟨stableT, ?_, ?_⟩
  · have kept := FillCompress.block_frame frame (p := off (work s) 7168) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      rw [dest']
      exact Offset.disjoint _ (by decide) (by decide) (by decide))
    rw [kept, keeps.mem, ← inputClear.work_eq]
    exact zeroClear.block
  · rw [dest'] at input
    exact input.trans (stableC.input h)

theorem prepare_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa prepare s (Prepared s · p pass lane slice counter) :=
  (prepare_layout_ok s h reads).mono (fun _ k =>
    ⟨k.stable, k.zero, k.input.trans (AddressHeader.input_spec p pass lane slice counter s words)⟩)

end VG.Proof.Argon2.AArch64.AddressCalls

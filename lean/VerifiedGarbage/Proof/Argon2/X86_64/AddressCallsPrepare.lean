import VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsStage
import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlock
import VerifiedGarbage.Proof.Argon2.AddressInput
import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderWords
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-! Merged from `Proof.Argon2.X86_64.AddressHeaderCorrect`. -/
section
/-! Merged from `Proof.Argon2.X86_64.AddressHeader`. -/
section
/-! Compose the seven input fields, preserving frame reads across every write. -/

namespace VG.Proof.Argon2.X86_64.AddressHeader

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressHeader

def value (s : State) (i : Nat) : Addr :=
  if i = 1 then s.gpr .rbx else if i = 2 then s.gpr .r14
  else s.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64

def headerMem (s : State) (p : Addr) : Nat → Mem
  | 0 => s.mem
  | n + 1 => (headerMem s p n).writeW (off p (8 * n)) (value s n)

theorem field_ok (s : State) (i : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) (frameOffset i)) 8)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (field i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i)) (value s i) ∧
      CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  unfold field value
  by_cases one : i = 1
  · simp only [one, ite_true]
    refine (registerWord_ok s 1 .rbx (one ▸ hw)).mono ?_
    rintro t ⟨mem, regs, rd, wr, mx⟩
    exact ⟨mem, ⟨fun r _ => congrFun regs r, rd, wr⟩, mx⟩
  · simp only [one, ite_false]
    by_cases two : i = 2
    · simp only [two, ite_true]
      refine (registerWord_ok s 2 .r14 (two ▸ hw)).mono ?_
      rintro t ⟨mem, regs, rd, wr, mx⟩
      exact ⟨mem, ⟨fun r _ => congrFun regs r, rd, wr⟩, mx⟩
    · simp only [two, ite_false]
      refine (frameWord_ok s i (frameOffset i) hr hw).mono ?_
      rintro t ⟨mem, regs, rd, wr, mx⟩
      exact ⟨mem, ⟨regs, rd, wr⟩, mx⟩

theorem offset_bound : ∀ i < 7, frameOffset i + 8 ≤ 272 := by decide +kernel

theorem offset_read (s : State) (i : Nat)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) (frameOffset i)) 8 := by
  apply reads
  unfold frameOffset
  split <;> [simp; skip]
  split <;> [simp; skip]
  split <;> [simp; skip]
  split <;> simp

theorem value_kept {s t : State} (keeps : CopyKeeps s t)
    (hf : Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (i : Nat) (hi : i < 7) : value t i = value s i := by
  unfold value
  rw [keeps.1 .rbx (by decide), keeps.1 .r14 (by decide), keeps.1 .rbp (by decide)]
  have read : t.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64 =
      s.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64 :=
    hf.readW (r := ⟨s.gpr .rbp, 272⟩)
      (Offset.contains_base _ (offset_bound i hi)
        (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) (offset_bound i hi)) (by decide)))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep) (by decide)
  rw [read]

theorem prefix_ok (n : Nat) (hn : n ≤ 7) (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa (.block (fields n)) s fun t =>
      t.mem = headerMem s (s.gpr .rdi) n ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, Frame.refl _ _, CopyKeeps.refl s, rfl⟩
  | succ n ih =>
    simp only [fields, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro a ⟨mem, frame, keeps, mx⟩
    have dest : a.gpr .rdi = s.gpr .rdi := keeps.1 .rdi (by decide)
    have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) (frameOffset n)) 8 := by
      rw [keeps.2.1, keeps.2.2, keeps.1 .rbp (by decide)]
      exact offset_read s n reads
    have writable : InRegions a.wr (off (a.gpr .rdi) (8 * n)) 8 := by
      rw [dest, keeps.2.2]
      exact write _ _ ⟨⟨s.gpr .rdi, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega) (by omega)⟩
    refine (field_ok a n read writable).mono ?_
    rintro t ⟨mem', keeps', mx'⟩
    have value' := value_kept keeps frame sep n (by omega)
    refine ⟨?_, ?_, keeps.trans keeps', mx'.trans mx⟩
    · rw [mem', dest, value', mem]
      rfl
    · rw [mem', dest]
      exact frame.writeW (r := ⟨s.gpr .rdi, 1024⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Argon2.X86_64.AddressHeader
end

/-! The prepared input agrees with RFC 9106's seven public address words. -/

namespace VG.Proof.Argon2.X86_64.AddressHeader

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressHeader

def input (s : State) : Block :=
  zeroBlock |>.set 0 (value s 0) |>.set 1 (value s 1) |>.set 2 (value s 2)
    |>.set 3 (value s 3) |>.set 4 (value s 4) |>.set 5 (value s 5) |>.set 6 (value s 6)

theorem headerMem_block (s : State) (p : Addr) (zero : blockAt s.mem p = zeroBlock) :
    blockAt (headerMem s p 7) p = input s := by
  rw [headerMem, blockAt_write_nat _ p 6 (by decide),
    headerMem, blockAt_write_nat _ p 5 (by decide),
    headerMem, blockAt_write_nat _ p 4 (by decide),
    headerMem, blockAt_write_nat _ p 3 (by decide),
    headerMem, blockAt_write_nat _ p 2 (by decide),
    headerMem, blockAt_write_nat _ p 1 (by decide),
    headerMem, blockAt_write_nat _ p 0 (by decide), headerMem, zero]
  rfl

theorem code_ok (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (zero : blockAt s.mem (s.gpr .rdi) = zeroBlock) :
    WP isa code s fun t => blockAt t.mem (s.gpr .rdi) = input s ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  refine (prefix_ok 7 (by decide) s reads write sep).mono ?_
  rintro t ⟨mem, frame, keeps, mx⟩
  exact ⟨by rw [mem]; exact headerMem_block s _ zero, frame, keeps, mx⟩

structure Words (p : Params) (pass lane slice counter : Nat) (s : State) : Prop where
  passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  laneWord : s.gpr .rbx = BitVec.ofNat 64 lane
  sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice
  blocksWord : s.mem.readW (off (s.gpr .rbp) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .rbp) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code
  counterWord : s.mem.readW (off (s.gpr .rbp) 8) 64 = BitVec.ofNat 64 counter

theorem input_spec (p : Params) (pass lane slice counter : Nat) (s : State)
    (h : Words p pass lane slice counter s) :
    input s = Proof.Argon2.addressInput p pass lane slice counter := by
  simp (config := {decide := true}) only [input, value, frameOffset,
    ite_true, ite_false, h.passWord, h.laneWord, h.sliceWord, h.blocksWord,
    h.passesWord, h.variantWord, h.counterWord, Proof.Argon2.addressInput]

theorem code_spec_ok (p : Params) (pass lane slice counter : Nat) (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (zero : blockAt s.mem (s.gpr .rdi) = zeroBlock)
    (words : Words p pass lane slice counter s) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .rdi) = Proof.Argon2.addressInput p pass lane slice counter ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr :=
  (code_ok s reads write sep zero).mono (fun _ h =>
    ⟨h.1.trans (input_spec p pass lane slice counter s words), h.2⟩)

end VG.Proof.Argon2.X86_64.AddressHeader
end

/-! Merged from `Proof.Argon2.X86_64.AddressCallsClear`. -/
section
/-! Clear an address-generation block, retaining the allocation invariants. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

structure Cleared (s t : State) (offset : Nat) : Prop where
  block : blockAt t.mem (off (work s) offset) = zeroBlock
  ready : Ready t
  work_eq : work t = work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (work s) offset, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem clearAt_ok (s : State) (h : Ready s) (offset : Nat) (bound : offset + 1024 ≤ 8192) :
    WP isa (clearAt offset) s (Cleared s · offset) := by
  unfold clearAt
  refine WP.seq ((pointer_ok s offset h.frameRead).mono ?_)
  rintro a ⟨dest, keeps⟩
  rw [displacement_eq offset (by omega)] at dest
  have write : Covers [⟨a.gpr .rdi, 1024⟩] a.wr := by
    rw [dest, keeps.wr]; exact work_cover s h offset 1024 bound
  refine (ClearBlock.code_ok a write).mono ?_
  rintro t ⟨zero, frame, tk, mx⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ≠ .rax ∧ r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r ne.1).trans (keeps.regs r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using ne.2))
  have rd := tk.2.1.trans keeps.rd
  have wr := tk.2.2.trans keeps.wr
  have hf : Frame [⟨off (work s) offset, 1024⟩] s.mem t.mem := by
    rw [dest, keeps.mem] at frame; exact frame
  have bigger : Frame (stageWrites s offset) s.mem t.mem :=
    hf.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [stageWrites])
  obtain ⟨ready, work'⟩ := ready_of_frame h offset bound regs rd wr bigger
  rw [dest] at zero
  exact ⟨zero, ready, work', regs, rd, wr, hf, mx.trans keeps.mxcsr⟩

theorem Cleared.full_frame {s t : State} {offset : Nat} (h : Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : Frame [⟨work s, 8192⟩] s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨work s, 8192⟩, by simp, Offset.sub_base _ bound⟩

theorem frame_word {s t : State} (h : Ready s) (frame : Frame [⟨work s, 8192⟩] s.mem t.mem)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 :=
  frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.frameWork) (by decide)

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Prepare the independent-address input and zero block from arbitrary scratch. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

structure Stable (s t : State) : Prop where
  ready : Ready t
  work_eq : work t = work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨work s, 8192⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem Stable.trans {s a t : State} (h : Stable s a) (k : Stable a t) : Stable s t := by
  have hf := k.frame
  rw [h.work_eq] at hf
  exact ⟨k.ready, k.work_eq.trans h.work_eq, fun r hr => (k.regs r hr).trans (h.regs r hr),
    k.rd.trans h.rd, k.wr.trans h.wr, h.frame.trans hf, k.mxcsr.trans h.mxcsr⟩

theorem Cleared.stable {s t : State} {offset : Nat} (h : Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : Stable s t :=
  ⟨h.ready, h.work_eq, h.regs, h.rd, h.wr, h.full_frame bound, h.mxcsr⟩

theorem stable_of_frame {s t : State} (h : Ready s)
    (regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (frame : Frame [⟨work s, 8192⟩] s.mem t.mem) (mx : t.mxcsr = s.mxcsr) : Stable s t := by
  have bp := regs .rbp (by simp [calleeSaved])
  have sp := regs .rsp (by simp [calleeSaved])
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
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (off (t.gpr .rbp) d) 8 := by
  rw [h.rd, h.wr, h.regs .rbp (by simp [calleeSaved])]
  exact reads

theorem Stable.words {s t : State} {p : Params} {pass lane slice counter : Nat} (ready : Ready s) (h : Stable s t)
    (words : AddressHeader.Words p pass lane slice counter s) :
    AddressHeader.Words p pass lane slice counter t := by
  have bp := h.regs .rbp (by simp [calleeSaved])
  have read (d : Nat) (hd : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [bp]; exact frame_word ready h.frame d hd
  exact ⟨(read 0 (by decide)).trans words.passWord,
    (h.regs .rbx (by simp [calleeSaved])).trans words.laneWord,
    (h.regs .r14 (by simp [calleeSaved])).trans words.sliceWord,
    (read 240 (by decide)).trans words.blocksWord,
    (read 72 (by decide)).trans words.passesWord,
    (read 112 (by decide)).trans words.variantWord,
    (read 8 (by decide)).trans words.counterWord⟩

theorem pointer_stable {s a : State} (h : Ready s)
    (k : Divide.Keeps [.rdi] s a) : Stable s a := by
  apply stable_of_frame h _ k.rd k.wr _ k.mxcsr
  · intro r hr
    apply k.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem Stable.input {s t : State} (ready : Ready s) (h : Stable s t) :
    AddressHeader.input t = AddressHeader.input s := by
  have value (i : Nat) (hi : i < 7) : AddressHeader.value t i = AddressHeader.value s i := by
    unfold AddressHeader.value
    rw [h.regs .rbx (by simp [calleeSaved]), h.regs .r14 (by simp [calleeSaved]),
      h.regs .rbp (by simp [calleeSaved]),
      frame_word ready h.frame (Impl.Argon2.X86_64.AddressHeader.frameOffset i)
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
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
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
  refine WP.seq ((pointer_ok b 5120 zeroClear.ready.frameRead).mono ?_)
  rintro c ⟨dest, keeps⟩
  rw [displacement_eq 5120 (by decide)] at dest
  have stableC := stableB.trans (pointer_stable zeroClear.ready keeps)
  have dest' : c.gpr .rdi = off (work s) 5120 := by rw [dest, stableB.work_eq]
  have write : Covers [⟨c.gpr .rdi, 1024⟩] c.wr := by
    rw [dest, keeps.wr]; exact work_cover b zeroClear.ready 5120 1024 (by decide)
  have sep : (⟨c.gpr .rbp, 272⟩ : Region).Disjoint ⟨c.gpr .rdi, 1024⟩ := by
    rw [dest', stableC.regs .rbp (by simp [calleeSaved])]
    exact h.frameWork.sub_right (Offset.sub_base _ (by decide))
  have zero : blockAt c.mem (c.gpr .rdi) = zeroBlock := by rw [dest', keeps.mem]; exact inputZero
  refine (AddressHeader.code_ok c (stableC.reads reads) write sep zero).mono ?_
  rintro t ⟨input, frame, tk, mx⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = c.gpr r := by
    intro r hr
    apply tk.1
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
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
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa prepare s (Prepared s · p pass lane slice counter) :=
  (prepare_layout_ok s h reads).mono (fun _ k =>
    ⟨k.stable, k.zero, k.input.trans (AddressHeader.input_spec p pass lane slice counter s words)⟩)

end VG.Proof.Argon2.X86_64.AddressCalls

import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressOperation

/-! Establish compression-and-write invariants from the frame and allocations. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillCompress

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

def prefixWrites (s : State) : List Region := [⟨off (s.gpr .x19) 16, 8⟩]

structure Ready (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .x19) 16) 8
  leftRead : Covers [⟨s.gpr .x0, 1024⟩] (s.rd ++ s.wr)
  rightRead : Covers [⟨s.gpr .x1, 1024⟩] (s.rd ++ s.wr)
  destinationWrite : Covers [⟨s.gpr .x6, 1024⟩] s.wr
  workWrite : Covers [⟨work s, 5120⟩] s.wr
  leftWork : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  rightWork : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  destinationWork : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨work s, 5120⟩
  leftFrame : (⟨s.gpr .x0, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  rightFrame : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  destinationFrame : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  stackLeft : (below s.sp 8).Disjoint ⟨s.gpr .x0, 1024⟩
  stackRight : (below s.sp 8).Disjoint ⟨s.gpr .x1, 1024⟩
  stackWork : (below s.sp 8).Disjoint ⟨work s, 5120⟩
  destinationStack : (⟨s.gpr .x6, 1024⟩ : Region).Disjoint (below s.sp 8)
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below s.sp 8)

structure Prepared (s t : State) : Prop where
  ready : OperationReady t
  dest : destination t = s.gpr .x6
  counter : pass t = pass s
  scratch : t.gpr .x3 = work s
  output : t.gpr .x2 = work s + 4096
  left : t.gpr .x0 = s.gpr .x0
  right : t.gpr .x1 = s.gpr .x1
  regs : ∀ r ∈ loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (prefixWrites s) s.mem t.mem
  leftBlock : blockAt t.mem (t.gpr .x0) = blockAt s.mem (s.gpr .x0)
  rightBlock : blockAt t.mem (t.gpr .x1) = blockAt s.mem (s.gpr .x1)
  oldBlock : blockAt t.mem (destination t) = blockAt s.mem (s.gpr .x6)

theorem block_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (p : Addr) (sep : ∀ r ∈ rs, (⟨p, 1024⟩ : Region).Disjoint r) :
    blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  have read : m'.readW (off p (8 * i)) 64 = m.readW (off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega) (by omega)) sep (by decide)
  rw [← blockAt_get m' p ⟨i, hi⟩, ← blockAt_get m p ⟨i, hi⟩] at read
  exact read

theorem work_cover (s : State) (h : Ready s) (d n : Nat) (hd : d + n ≤ 5120) :
    Covers [⟨off (work s) d, n⟩] s.wr := by
  have sub : Covers [⟨off (work s) d, n⟩] [⟨work s, 5120⟩] := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨work s, 5120⟩, by simp, d, rfl, hd⟩
  exact fun p n hp => h.workWrite p n (sub p n hp)

theorem prepared_of_setup (s a b : State) (h : Ready s)
    (mem : a.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6))
    (regs : a.gpr = s.gpr) (rd : a.rd = s.rd) (wr : a.wr = s.wr) (sp : a.sp = s.sp)
    (scratch : b.gpr .x3 = a.mem.readW (off (a.gpr .x19) 248) 64)
    (output : b.gpr .x2 = a.mem.readW (off (a.gpr .x19) 248) 64 + 4096)
    (keeps : Divide.Keeps [.x3, .x2, .x12, .x15] a b) : Prepared s b := by
  have g (r : Reg) (hr : r ∉ [Reg.x3, .x2, .x12, .x15]) : b.gpr r = s.gpr r :=
    (keeps.regs r hr).trans (congrFun regs r)
  have brd : b.rd = s.rd := keeps.rd.trans rd
  have bwr : b.wr = s.wr := keeps.wr.trans wr
  have bsp : b.sp = s.sp := keeps.sp.trans sp
  have bm : b.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6) := keeps.mem.trans mem
  have unchanged (d : Nat) (sep : d + 8 ≤ 16 ∨ 24 ≤ d) (bound : d + 8 ≤ 272) :
      b.mem.readW (off (b.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bm, g .x19 (by decide)]
    exact Mem.readW_writeW_sep (Offset.sep _ sep (by omega) (by decide)) (by decide)
  have work' : b.gpr .x3 = work s := by
    rw [scratch, regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have out' : b.gpr .x2 = work s + 4096 := by
    rw [output, regs, mem,
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), work]
  have dest : destination b = s.gpr .x6 := by
    unfold destination
    rw [bm, g .x19 (by decide), Mem.readW_writeW_self64]
  have counter : pass b = pass s := unchanged 0 (by decide) (by decide)
  have frame : Frame (prefixWrites s) s.mem b.mem := by
    rw [bm]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .x19) 16, 8⟩) (by simp [prefixWrites]) _
      (Region.contains_self _ _)
  have cellFrame (p : Addr) (sep : (⟨p, 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩) :
      blockAt b.mem p = blockAt s.mem p :=
    block_frame frame p (by
      intro r hr
      simp only [prefixWrites, List.mem_singleton] at hr
      subst r
      exact sep.sub_right (Offset.sub_base _ (by decide)))
  have tempSub : Region.Sub ⟨work s + 4096, 1024⟩ ⟨work s, 5120⟩ :=
    Offset.sub_base _ (by decide)
  have scratchSub : Region.Sub ⟨work s, 4096⟩ ⟨work s, 5120⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, dest, counter, work', out', g .x0 (by decide), g .x1 (by decide), ?_, brd, bwr, bsp,
    frame, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [g .x0 (by decide), brd, bwr]; exact h.leftRead
      · rw [g .x1 (by decide), brd, bwr]; exact h.rightRead
      · rw [out', bwr]; exact work_cover s h 4096 1024 (by decide)
      · rw [work', bwr]
        simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
          using work_cover s h 0 4096 (by decide)
      · rw [g .x0 (by decide), work']; exact h.leftWork.sub_right scratchSub
      · rw [g .x1 (by decide), work']; exact h.rightWork.sub_right scratchSub
      · rw [out', work']; exact Offset.disjoint_base _ (by decide) (by decide)
      · rw [bsp, g .x0 (by decide)]; exact h.stackLeft
      · rw [bsp, g .x1 (by decide)]; exact h.stackRight
      · rw [bsp, out']; exact h.stackWork.sub_right tempSub
      · rw [bsp, work']; exact h.stackWork.sub_right scratchSub
    · intro d hd
      rw [brd, bwr, g .x19 (by decide)]; exact h.frameRead d hd
    · rw [unchanged 248 (by decide) (by decide), work']; rfl
    · rw [work', out']
    · rw [dest, bwr]; exact h.destinationWrite
    · intro r hr
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g .x19 (by decide), out']; exact h.frameWork.sub_right tempSub
      · rw [g .x19 (by decide), work']; exact h.frameWork.sub_right scratchSub
      · rw [g .x19 (by decide), bsp]; exact h.frameStack
    · intro r hr
      rw [dest]
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [out']; exact h.destinationWork.sub_right tempSub
      · rw [work']; exact h.destinationWork.sub_right scratchSub
      · rw [bsp]; exact h.destinationStack
  · intro r hr
    apply g r
    simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [g .x0 (by decide)]; exact cellFrame _ h.leftFrame
  · rw [g .x1 (by decide)]; exact cellFrame _ h.rightFrame
  · rw [dest]; exact cellFrame _ h.destinationFrame

theorem setup_ok (s : State) (h : Ready s) :
    WP isa setup s (Prepared s) := by
  unfold setup
  refine WP.seq ((saveCurrent_ok s h.frameWrite).mono ?_)
  rintro a ⟨mem, regs, rd, wr, sp⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 248) 8 := by
    rw [rd, wr, regs]; exact h.frameRead 248 (by simp)
  refine (compressArgs_ok a read).mono ?_
  rintro b ⟨scratch, output, keeps⟩
  exact prepared_of_setup s a b h mem regs rd wr sp scratch output keeps

end VG.Proof.Argon2.AArch64.FillCompress

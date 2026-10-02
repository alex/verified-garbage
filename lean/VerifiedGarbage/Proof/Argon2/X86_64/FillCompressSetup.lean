import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressOperation

/-! Establish compression-and-write invariants from the frame and allocations. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillCompress

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

def prefixWrites (s : State) : List Region := [⟨off (s.gpr .rbp) 16, 8⟩]

structure Ready (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .rbp) 16) 8
  leftRead : Covers [⟨s.gpr .rdi, 1024⟩] (s.rd ++ s.wr)
  rightRead : Covers [⟨s.gpr .rsi, 1024⟩] (s.rd ++ s.wr)
  destinationWrite : Covers [⟨s.gpr .r10, 1024⟩] s.wr
  workWrite : Covers [⟨work s, 5120⟩] s.wr
  leftWork : (⟨s.gpr .rdi, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  rightWork : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  destinationWork : (⟨s.gpr .r10, 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨work s, 5120⟩
  leftFrame : (⟨s.gpr .rdi, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  rightFrame : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  destinationFrame : (⟨s.gpr .r10, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  stackLeft : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdi, 1024⟩
  stackRight : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rsi, 1024⟩
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨work s, 5120⟩
  destinationStack : (⟨s.gpr .r10, 1024⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)

structure Prepared (s t : State) : Prop where
  ready : OperationReady t
  dest : destination t = s.gpr .r10
  counter : pass t = pass s
  scratch : t.gpr .rcx = work s
  output : t.gpr .rdx = work s + 4096
  left : t.gpr .rdi = s.gpr .rdi
  right : t.gpr .rsi = s.gpr .rsi
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (prefixWrites s) s.mem t.mem
  leftBlock : blockAt t.mem (t.gpr .rdi) = blockAt s.mem (s.gpr .rdi)
  rightBlock : blockAt t.mem (t.gpr .rsi) = blockAt s.mem (s.gpr .rsi)
  oldBlock : blockAt t.mem (destination t) = blockAt s.mem (s.gpr .r10)

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
    (mem : a.mem = s.mem.writeW (off (s.gpr .rbp) 16) (s.gpr .r10))
    (regs : a.gpr = s.gpr) (rd : a.rd = s.rd) (wr : a.wr = s.wr)
    (scratch : b.gpr .rcx = a.mem.readW (off (a.gpr .rbp) 248) 64)
    (output : b.gpr .rdx = a.mem.readW (off (a.gpr .rbp) 248) 64 + 4096)
    (keeps : Divide.Keeps [.rcx, .rdx] a b) : Prepared s b := by
  have g (r : Reg) (hr : r ∉ [Reg.rcx, .rdx]) : b.gpr r = s.gpr r :=
    (keeps.regs r hr).trans (congrFun regs r)
  have brd : b.rd = s.rd := keeps.rd.trans rd
  have bwr : b.wr = s.wr := keeps.wr.trans wr
  have bm : b.mem = s.mem.writeW (off (s.gpr .rbp) 16) (s.gpr .r10) := keeps.mem.trans mem
  have unchanged (d : Nat) (sep : d + 8 ≤ 16 ∨ 24 ≤ d) (bound : d + 8 ≤ 272) :
      b.mem.readW (off (b.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [bm, g .rbp (by decide)]
    exact Mem.readW_writeW_sep (Offset.sep _ sep (by omega) (by decide)) (by decide)
  have work' : b.gpr .rcx = work s := by
    rw [scratch, regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have out' : b.gpr .rdx = work s + 4096 := by
    rw [output, regs, mem,
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), work]
  have dest : destination b = s.gpr .r10 := by
    unfold destination
    rw [bm, g .rbp (by decide), Mem.readW_writeW_self64]
  have counter : pass b = pass s := unchanged 0 (by decide) (by decide)
  have frame : Frame (prefixWrites s) s.mem b.mem := by
    rw [bm]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .rbp) 16, 8⟩) (by simp [prefixWrites]) _
      (Region.contains_self _ _)
  have cellFrame (p : Addr) (sep : (⟨p, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩) :
      blockAt b.mem p = blockAt s.mem p :=
    block_frame frame p (by
      intro r hr
      simp only [prefixWrites, List.mem_singleton] at hr
      subst r
      exact sep.sub_right (Offset.sub_base _ (by decide)))
  have tempSub : Region.Sub ⟨work s + 4096, 1024⟩ ⟨work s, 5120⟩ :=
    Offset.sub_base _ (by decide)
  have scratchSub : Region.Sub ⟨work s, 4096⟩ ⟨work s, 5120⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, dest, counter, work', out', g .rdi (by decide), g .rsi (by decide), ?_, brd, bwr,
    frame, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [g .rdi (by decide), brd, bwr]; exact h.leftRead
      · rw [g .rsi (by decide), brd, bwr]; exact h.rightRead
      · rw [out', bwr]; exact work_cover s h 4096 1024 (by decide)
      · rw [work', bwr]
        simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
          using work_cover s h 0 4096 (by decide)
      · rw [g .rdi (by decide), work']; exact h.leftWork.sub_right scratchSub
      · rw [g .rsi (by decide), work']; exact h.rightWork.sub_right scratchSub
      · rw [out', work']; exact Offset.disjoint_base _ (by decide) (by decide)
      · rw [g .rsp (by decide), g .rdi (by decide)]; exact h.stackLeft
      · rw [g .rsp (by decide), g .rsi (by decide)]; exact h.stackRight
      · rw [g .rsp (by decide), out']; exact h.stackWork.sub_right tempSub
      · rw [g .rsp (by decide), work']; exact h.stackWork.sub_right scratchSub
    · intro d hd
      rw [brd, bwr, g .rbp (by decide)]; exact h.frameRead d hd
    · rw [unchanged 248 (by decide) (by decide), work']; rfl
    · rw [work', out']
    · rw [dest, bwr]; exact h.destinationWrite
    · intro r hr
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g .rbp (by decide), out']; exact h.frameWork.sub_right tempSub
      · rw [g .rbp (by decide), work']; exact h.frameWork.sub_right scratchSub
      · rw [g .rbp (by decide), g .rsp (by decide)]; exact h.frameStack
    · intro r hr
      rw [dest]
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [out']; exact h.destinationWork.sub_right tempSub
      · rw [work']; exact h.destinationWork.sub_right scratchSub
      · rw [g .rsp (by decide)]; exact h.destinationStack
  · intro r hr
    apply g r
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [g .rdi (by decide)]; exact cellFrame _ h.leftFrame
  · rw [g .rsi (by decide)]; exact cellFrame _ h.rightFrame
  · rw [dest]; exact cellFrame _ h.destinationFrame

theorem setup_ok (s : State) (h : Ready s) :
    WP isa setup s (Prepared s) := by
  unfold setup
  refine WP.seq ((saveCurrent_ok s h.frameWrite).mono ?_)
  rintro a ⟨mem, regs, rd, wr, _⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 248) 8 := by
    rw [rd, wr, regs]; exact h.frameRead 248 (by simp)
  refine (compressArgs_ok a read).mono ?_
  rintro b ⟨scratch, output, keeps⟩
  exact prepared_of_setup s a b h mem regs rd wr scratch output keeps

end VG.Proof.Argon2.X86_64.FillCompress

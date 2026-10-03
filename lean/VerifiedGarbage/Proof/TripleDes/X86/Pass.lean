import VerifiedGarbage.Proof.TripleDes.X86.PassStart
namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

structure PassPost (keys : DesSchedule) (d : Direction) (origin : State)
    (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .esi = (roundPrefix keys d 16 v).2
  right : s.gpr .edi = (roundPrefix keys d 16 v).1
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  base : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [workRegion origin] origin.mem s.mem

theorem roundsWithSwap_ok (keys : DesSchedule) (d : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (hok : Ok sboxCfg origin)
    (hl : origin.gpr .esi = v.1) (hr : origin.gpr .edi = v.2)
    (hptr : roundKeyPtr origin = keyAddr base d 0) (hcount : roundCount origin = 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base d j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base d j) t, 4⟩ : Region).Disjoint (workRegion origin))
    (hslots : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (origin.gpr .ebp) k) 4 (wordAddr (keyAddr base d j) t) 4)
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base d j)).setWidth 48 = roundKey keys d j) :
    WP isa (.seq (.loop (.block (roundBody ++ roundAdvance d)) .ne) (.block swapHalves))
      origin (PassPost keys d origin v) := by
  apply WP.seq
  apply WP.mono (roundsLoop_ok keys d base origin v hok hl hr hptr hcount hread hsep hslots hkeys)
  intro s hs
  obtain ⟨s', run, left, right, rd, wr, mem, keptBase, keptSp⟩ := swapHalves_ok s
  apply WP.of_runBlock
  refine ⟨s', run, left.trans hs.right, right.trans hs.left, rd.trans hs.rd, wr.trans hs.wr,
    keptBase.trans hs.base, keptSp.trans hs.sp, ?_⟩
  rw [mem]; exact hs.frame

theorem pass_ok (c : Nat) (keys : DesSchedule) (d : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (hok : Ok sboxCfg origin)
    (hl : origin.gpr .esi = v.1) (hr : origin.gpr .edi = v.2)
    (hptr : startAddr c d origin = keyAddr base d 0)
    (harg : InRegions (origin.rd ++ origin.wr) (wordAddr (origin.gpr .esp) 1) 4)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base d j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base d j) t, 4⟩ : Region).Disjoint (workRegion origin))
    (hslots : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (origin.gpr .ebp) k) 4 (wordAddr (keyAddr base d j) t) 4)
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base d j)).setWidth 48 = roundKey keys d j) :
    WP isa (pass c d) origin (PassPost keys d origin v) := by
  obtain ⟨s, run, mem, rd, wr, regs⟩ := passStart_ok c d origin hok harg
  have keptBase := regs .ebp (by decide)
  have keptSp := regs .esp (by decide)
  have hwork : workRegion s = workRegion origin := by simp only [workRegion, keptBase]
  have hf : Frame [workRegion origin] origin.mem s.mem := by
    rw [mem]; exact start_frame c d origin hok.fit
  have hkeysS : ∀ j < 16, (readKey s.mem (keyAddr base d j)).setWidth 48 = roundKey keys d j := by
    intro j hj
    have heq := readKey_frame hf (ptr := keyAddr base d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep j hj t ht)
    exact (congrArg (BitVec.setWidth 48) heq).trans (hkeys j hj)
  have hreadS : ∀ j < 16, ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (keyAddr base d j) t) 4 := by
    rw [rd, wr]; exact hread
  have hsepS : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base d j) t, 4⟩ : Region).Disjoint (workRegion s) := by
    rw [hwork]; exact hsep
  have hslotsS : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (s.gpr .ebp) k) 4 (wordAddr (keyAddr base d j) t) 4 := by
    rw [keptBase]; exact hslots
  have start := start_pointer c d origin s keptBase mem hok.fit
  have htail := roundsWithSwap_ok keys d base s v (hok.congr keptBase keptBase rd wr)
    ((regs .esi (by decide)).trans hl) ((regs .edi (by decide)).trans hr)
    (start.1.trans hptr) start.2 hreadS hsepS hslotsS hkeysS
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨s, run, WP.mono htail ?_⟩
  intro s' hs
  refine ⟨hs.left, hs.right, hs.rd.trans rd, hs.wr.trans wr, hs.base.trans keptBase,
    hs.sp.trans keptSp, ?_⟩
  have hframe := hs.frame
  rw [hwork] at hframe
  exact hf.trans hframe
end VG.Proof.TripleDes.X86

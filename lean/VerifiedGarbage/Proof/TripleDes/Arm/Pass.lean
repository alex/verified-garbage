import VerifiedGarbage.Proof.TripleDes.Arm.PassStart

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

structure PassPost (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r10 = (roundPrefix keys direction 16 v).2
  right : s.gpr .r11 = (roundPrefix keys direction 16 v).1
  pointer : s.gpr .r0 = endPointer base direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

/-- The sixteen-round loop and final DES half swap. -/
theorem roundsWithSwap_ok (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : origin.gpr .r0 = keyAddr base direction 0)
    (hcount : origin.gpr .r9 = BitVec.ofNat 32 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.seq (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      (.block swapHalves)) origin (PassPost keys direction base origin v) := by
  apply WP.seq
  apply WP.mono (roundsLoop_ok keys direction base origin v hok hl hr hptr hcount
    hread hsep hkeys)
  intro s hs
  obtain ⟨s', run, left, right, rd, wr, sp, mem, regs⟩ := swapHalves_ok s
  apply WP.of_runBlock
  refine ⟨s', run, left.trans hs.right, right.trans hs.left, (regs .r0 (by decide)).trans hs.pointer,
    rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, ?_, ?_⟩
  · intro q hq
    have hkeep : ∀ r ∈ roundStepKept, r ∈ roundOuterKept := by decide
    exact (regs q (hkeep q hq)).trans (hs.regs q hq)
  · rw [mem]
    exact hs.frame


theorem pass_ok (offset : Int) (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true)
    (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : startPointer (origin.gpr .r0) offset =
      keyAddr base direction 0)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (pass offset direction) origin (PassPost keys direction base origin v) := by
  obtain ⟨s, run, ptr, count, mem, rd, wr, sp, regs⟩ := passStart_ok offset origin ho
  have hbase : s.gpr .r2 = origin.gpr .r2 := regs .r2 (by decide) (by decide)
  have hwork : spillRegion s = spillRegion origin := by simp only [spillRegion, hbase]
  have hkeysS : ∀ j < 16, (readKey s.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j := by rw [mem]; exact hkeys
  have hreadS : ∀ j < 16, ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (keyAddr base direction j) t) 4 := by
    rw [rd, wr]; exact hread
  have hsepS : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion s) := by
    rw [hwork]; exact hsep
  have htail := roundsWithSwap_ok keys direction base s v
    (hok.congr hbase hbase rd wr)
    ((regs .r10 (by decide) (by decide)).trans hl)
    ((regs .r11 (by decide) (by decide)).trans hr)
    (ptr.trans hptr) count hreadS hsepS hkeysS
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨s, run, WP.mono htail ?_⟩
  intro s' hs
  refine ⟨hs.left, hs.right, hs.pointer, hs.rd.trans rd, hs.wr.trans wr, hs.sp.trans sp, ?_, ?_⟩
  · intro q hq
    have hneq : ∀ r ∈ roundStepKept, r ≠ .r9 ∧ r ≠ .r0 := by decide
    exact (hs.regs q hq).trans (regs q (hneq q hq).2 (hneq q hq).1)
  · have hf := hs.frame
    rw [hwork, mem] at hf
    exact hf

end VG.Proof.TripleDes.Arm

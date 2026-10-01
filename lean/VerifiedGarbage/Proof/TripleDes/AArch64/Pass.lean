import VerifiedGarbage.Proof.TripleDes.AArch64.PassStart

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

structure PassPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .x19 = (roundPrefix keys direction 16 v).2.setWidth 64
  right : s.gpr .x20 = (roundPrefix keys direction 16 v).1.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

/-- The sixteen-round loop and final DES half swap. -/
theorem roundsWithSwap_ok (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .x19 = v.1.setWidth 64) (hr : origin.gpr .x20 = v.2.setWidth 64)
    (hptr : origin.gpr .x22 = keyAddr base direction 0)
    (hcount : origin.gpr .x21 = BitVec.ofNat 64 16)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.seq (.loop (.block (roundBody ++ roundAdvance direction)) (.nonzero .x .x21))
      (.block swapHalves)) origin (PassPost keys direction origin v) := by
  apply WP.seq
  apply WP.mono (roundsLoop_ok keys direction base origin v hok hl hr hptr hcount
    hread hsep hkeys)
  intro s hs
  obtain ⟨s', run, left, right, rd, wr, sp, mem, regs⟩ := swapHalves_ok s
  apply WP.of_runBlock
  refine ⟨s', run, left.trans hs.right, right.trans hs.left,
    rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, ?_, ?_⟩
  · intro q hq
    have hkeep : ∀ r ∈ roundStepKept, r ∈ roundOuterKept := by decide
    exact (regs q (hkeep q hq)).trans (hs.regs q hq)
  · rw [mem]
    exact hs.frame


theorem pass_ok (component : Nat) (hc : component < 3)
    (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .x19 = v.1.setWidth 64) (hr : origin.gpr .x20 = v.2.setWidth 64)
    (hptr : origin.gpr .x0 + BitVec.ofNat 64 (passOffset component direction) =
      keyAddr base direction 0)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (pass component direction) origin (PassPost keys direction origin v) := by
  obtain ⟨s, run, ptr, count, mem, rd, wr, sp, regs⟩ := passStart_ok component hc direction origin
  have hbase : s.gpr .x2 = origin.gpr .x2 := regs .x2 (by decide) (by decide)
  have hwork : spillRegion s = spillRegion origin := by simp only [spillRegion, hbase]
  have hkeysS : ∀ j < 16, (s.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j := by rw [mem]; exact hkeys
  have hreadS : ∀ j < 16, InRegions (s.rd ++ s.wr) (keyAddr base direction j) 8 := by
    rw [rd, wr]; exact hread
  have hsepS : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (spillRegion s) := by
    rw [hwork]; exact hsep
  have htail := roundsWithSwap_ok keys direction base s v
    (hok.congr hbase hbase rd wr)
    ((regs .x19 (by decide) (by decide)).trans hl)
    ((regs .x20 (by decide) (by decide)).trans hr)
    (ptr.trans hptr) count hreadS hsepS hkeysS
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨s, run, WP.mono htail ?_⟩
  intro s' hs
  refine ⟨hs.left, hs.right, hs.rd.trans rd, hs.wr.trans wr, hs.sp.trans sp, ?_, ?_⟩
  · intro q hq
    have hneq : ∀ r ∈ roundStepKept, r ≠ .x21 ∧ r ≠ .x22 := by decide
    exact (hs.regs q hq).trans (regs q (hneq q hq).1 (hneq q hq).2)
  · have hf := hs.frame
    rw [hwork, mem] at hf
    exact hf

end VG.Proof.TripleDes.AArch64

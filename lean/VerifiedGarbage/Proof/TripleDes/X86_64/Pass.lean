import VerifiedGarbage.Proof.TripleDes.X86_64.PassStart

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

structure PassPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r12 = (roundPrefix keys direction 16 v).2.setWidth 64
  right : s.gpr .r13 = (roundPrefix keys direction 16 v).1.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [workRegion origin] origin.mem s.mem

/-- The sixteen-round loop and final DES half swap. -/
theorem roundsWithSwap_ok (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r12 = v.1.setWidth 64) (hr : origin.gpr .r13 = v.2.setWidth 64)
    (hptr : origin.gpr .rdi = keyAddr base direction 0)
    (hcount : origin.mem.readW (countAddr origin) 64 = BitVec.ofNat 64 16)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (countAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (workRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.seq (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      (.block swapHalves)) origin (PassPost keys direction origin v) := by
  apply WP.seq
  apply WP.mono (roundsLoop_ok keys direction base origin v hok hl hr hptr hcount
    hcountRead hcountWrite hread hsep hkeys)
  intro s hs
  obtain ⟨s', run, left, right, rd, wr, mem, regs⟩ := swapHalves_ok s
  apply WP.of_runBlock
  refine ⟨s', run, left.trans hs.right, right.trans hs.left,
    rd.trans hs.rd, wr.trans hs.wr, ?_, ?_⟩
  · intro q hq
    have hkeep : ∀ r ∈ [Reg.rsi, .rdx, .rsp], r ∈ roundOuterKept := by decide
    exact (regs q (hkeep q hq)).trans (hs.regs q hq)
  · rw [mem]
    exact hs.frame


/-- A complete DES pass, including its public key-pointer and counter setup. -/
theorem pass_ok (component : Nat) (hc : component < 3)
    (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r12 = v.1.setWidth 64) (hr : origin.gpr .r13 = v.2.setWidth 64)
    (hptr : origin.mem.readW (savedKeyAddr origin) 64 +
      BitVec.ofNat 64 (passOffset component direction) = keyAddr base direction 0)
    (hsavedRead : InRegions (origin.rd ++ origin.wr) (savedKeyAddr origin) 8)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (countAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (workRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (pass component direction) origin (PassPost keys direction origin v) := by
  obtain ⟨s, run, ptr, mem, rd, wr, regs⟩ :=
    passStart_ok component hc direction origin hsavedRead hcountWrite
  have hbase : s.gpr .rdx = origin.gpr .rdx := regs .rdx (by decide) (by decide)
  have hcountAddr : countAddr s = countAddr origin := congrArg (· + BitVec.ofNat 64 56) hbase
  have hwork : workRegion s = workRegion origin := congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 392⟩ : Region)) hbase
  have hframe : Frame [workRegion origin] origin.mem s.mem := by
    rw [mem]
    apply (countWrite_frame origin.mem (countAddr origin) (BitVec.ofNat 64 16)).sub
    intro r hmem
    obtain rfl := List.mem_singleton.mp hmem
    exact ⟨workRegion origin, List.mem_singleton_self _, count_sub_work origin⟩
  have hkeysS : ∀ j < 16, (s.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j := by
    intro j hj
    have hmem := hframe.readW (a := keyAddr base direction j) (w := 64)
      (r := ⟨keyAddr base direction j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep j hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys j hj)
  have hreadS : ∀ j < 16, InRegions (s.rd ++ s.wr) (keyAddr base direction j) 8 := by
    rw [rd, wr]; exact hread
  have hsepS : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (workRegion s) := by
    rw [hwork]; exact hsep
  have hcountReadS : InRegions (s.rd ++ s.wr) (countAddr s) 8 := by
    rw [rd, wr, hcountAddr]; exact hcountRead
  have hcountWriteS : InRegions s.wr (countAddr s) 8 := by
    rw [wr, hcountAddr]; exact hcountWrite
  have hcount : s.mem.readW (countAddr s) 64 = BitVec.ofNat 64 16 := by
    rw [mem, hcountAddr]
    exact Mem.readW_writeW_self64 _ _ _
  have htail := roundsWithSwap_ok keys direction base s v
    (hok.congr hbase hbase rd wr)
    ((regs .r12 (by decide) (by decide)).trans hl)
    ((regs .r13 (by decide) (by decide)).trans hr)
    (ptr.trans hptr) hcount hcountReadS hcountWriteS hreadS hsepS hkeysS
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨s, run, WP.mono htail ?_⟩
  intro s' hs
  refine ⟨hs.left, hs.right, hs.rd.trans rd, hs.wr.trans wr, ?_, ?_⟩
  · intro q hq
    have hneq : ∀ r ∈ [Reg.rsi, .rdx, .rsp], r ≠ .rax ∧ r ≠ .rdi := by decide
    exact (hs.regs q hq).trans (regs q (hneq q hq).1 (hneq q hq).2)
  · have hf := hs.frame
    rw [hwork] at hf
    exact hframe.trans hf

end VG.Proof.TripleDes.X86_64

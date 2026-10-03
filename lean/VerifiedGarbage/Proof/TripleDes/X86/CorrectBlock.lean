import VerifiedGarbage.Proof.TripleDes.X86.Pre

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 argContainsCount)
open VG.Spec.TripleDes (Direction)

theorem block_correct (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (block d) s (fun s' => abiPreserved s s' ∧ (blockContract d).post s s') := by
  have hp := headPre_of_contract d s hs
  obtain ⟨_, hwr, _, _, _, argsScratch, retData, retScratch, _, dataFit, _, spFit⟩ := hs
  have hwrite : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4 := by
    intro i hi
    rw [data_argument, wordAddr, addr_eq (by omega), hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    obtain ⟨r, hr, hc⟩ := hp.saveWrite i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion (prepared s)) := by
    have sub : Region.Sub ⟨wordAddr (s.gpr .esp) 2, 4⟩ ⟨argAddr s 0, 12⟩ := by
      rw [wordAddr, addr_eq (by omega), VG.Proof.Rc2.X86.argAddr_eq s 0 (by omega)]
      exact Offset.sub _ (by decide) (by decide)
    have workSub : Region.Sub (workRegion (prepared s)) ⟨addr32 (arg s 2), 512⟩ := by
      unfold workRegion prepared
      rw [VG.X86.RegUpd.gpr_setReg_self, scratch_argument]
      exact Offset.sub_base _ (by decide)
    exact (argsScratch.sub_left sub).sub_right workSub
  apply WP.mono (block_ok (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0)))
    (arg s 0) d s hp hread hwrite hargSep)
  intro s' hpost
  refine ⟨⟨?_, ?_⟩, hpost.result⟩
  · intro r hr
    have hregs : ∀ r ∈ calleeSaved, r ∈ savedRegs ∨ r = .esp := by decide
    rcases hregs r hr with h | rfl
    · exact hpost.saved r h
    · exact hpost.sp
  · apply hpost.frame.readW (r := ⟨addr32 (s.gpr .esp), 4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [blockRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact retData
    · exact retScratch

end VG.Proof.TripleDes.X86

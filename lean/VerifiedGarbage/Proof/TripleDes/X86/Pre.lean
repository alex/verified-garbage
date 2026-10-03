import VerifiedGarbage.Proof.TripleDes.X86.Contract
import VerifiedGarbage.Proof.TripleDes.X86.ScheduleMemory

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32 argContainsCount)
open VG.Spec.TripleDes (Direction)

theorem argument_word (s : State) (i : Nat) : arg s i = s.mem.readW (wordAddr (s.gpr .esp) (i + 1)) 32 := by
  unfold arg argAddr
  apply congrArg (fun p => s.mem.readW p 32)
  change addr (s.gpr .esp) (4 + 4 * i) = addr (s.gpr .esp) (4 * (i + 1))
  exact congrArg (addr (s.gpr .esp)) (by omega)

theorem data_argument (s : State) : dataArg s = arg s 1 := (argument_word s 1).symm

theorem scratch_argument (s : State) : scratchArg s 3 = arg s 2 := (argument_word s 2).symm

theorem schedule_argument (s : State) : scheduleArg s = arg s 0 := (argument_word s 0).symm

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0))))
      (arg s 0) s := by
  obtain ⟨hrd, hwr, keySep, dataSep, argsData, argsScratch, _, _, keyFit, dataFit, scratchFit, spFit⟩ := hs
  have bp : (prepared s).gpr .ebp = arg s 2 := by rw [prepared, gpr_setReg_self, scratch_argument]
  have sp : (prepared s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨addr32 (arg s 2), 512⟩ := by
    rw [saveRegion, scratch_argument]
    exact Region.sub_prefix (by decide)
  have workSub : Region.Sub (workRegion (prepared s)) ⟨addr32 (arg s 2), 512⟩ := by
    rw [workRegion, bp]
    exact Offset.sub_base _ (by decide)
  have argContains : ∀ i ∈ [1, 2, 3], (⟨argAddr s 0, 12⟩ : Region).Contains
      (wordAddr (s.gpr .esp) i) 4 := by
    intro i hi
    have hb : 1 ≤ i ∧ i ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    rw [wordAddr, addr_eq (by omega)]
    have h := argContainsCount s 3 spFit (i - 1) (by omega)
    rw [show 4 + 4 * (i - 1) = 4 * i by omega] at h
    exact h
  have argSub : ∀ i ∈ [1, 2, 3], Region.Sub ⟨wordAddr (s.gpr .esp) i, 4⟩ ⟨argAddr s 0, 12⟩ := by
    intro i hi a ha
    exact (argContains i hi).byte (by change (a - wordAddr (s.gpr .esp) i).toNat + 1 ≤ 4 at ha; omega)
  have argRead : ∀ i ∈ [1, 2, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    intro i hi
    rw [hrd, hwr]
    exact ⟨⟨argAddr s 0, 12⟩, by simp, argContains i hi⟩
  have slots : ∀ i < 128, InRegions (prepared s).wr (wordAddr ((prepared s).gpr .ebp) i) 4 := by
    intro i hi
    rw [bp, wordAddr, addr_eq (by omega)]
    change InRegions s.wr _ 4
    rw [hwr]
    exact ⟨⟨addr32 (arg s 2), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hok : Ok sboxCfg (prepared s) := by
    refine ⟨slots, ?_, ?_, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · change ((prepared s).gpr .ebp).toNat + 512 ≤ 2 ^ 32
      rw [bp]; exact scratchFit
    · intro k hk j hj; change j < 0 at hj; omega
  have hb : scheduleArg (prepared s) = arg s 0 := by
    unfold scheduleArg
    rw [sp]
    exact (argument_word s 0).symm
  have ready := ready_of_regions (prepared s) (arg s 0) hok hb keyFit
    (by intro p hp
        change InRegions (s.rd ++ s.wr) p 4
        rw [hrd, hwr]
        exact ⟨⟨addr32 (arg s 0), 384⟩, by simp, hp⟩)
    (by rw [bp]; exact keySep)
    (by change InRegions (s.rd ++ s.wr) (wordAddr ((prepared s).gpr .esp) 1) 4
        rw [sp]; exact argRead 1 (by decide))
    (by rw [sp]; exact (argsScratch.sub_left (argSub 1 (by decide))).sub_right workSub)
  refine ⟨ready, ?_, ?_, ?_, argRead, ?_, ?_, dataSep.sub_right saveSub, ?_⟩
  · rw [scratch_argument]; exact scratchFit
  · rw [data_argument]; exact dataFit
  · intro i hi
    rw [scratch_argument, hwr]
    exact ⟨⟨addr32 (arg s 2), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro i hi
    exact (argsScratch.sub_left (argSub i hi)).sub_right saveSub
  · intro i hi
    rw [data_argument, wordAddr, addr_eq (by omega), hrd, hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro c hc direction j hj t ht
    have keySub : Region.Sub ⟨wordAddr (keyAddr (componentBase (arg s 0) c) direction j) t, 4⟩
        ⟨addr32 (arg s 0), 384⟩ := by
      rw [keyWordAddress _ keyFit c j t hc hj ht direction]
      have bound := selectedRound_bound direction j hj
      exact Offset.sub_base _ (by omega)
    exact (keySep.sub_left keySub).sub_right saveSub

end VG.Proof.TripleDes.X86

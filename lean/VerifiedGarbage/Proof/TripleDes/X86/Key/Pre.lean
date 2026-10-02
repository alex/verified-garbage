import VerifiedGarbage.Proof.TripleDes.X86.Key.Contract

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd
open VG.Proof.Rc2.X86 (addr32 argContainsCount)

theorem key_argument (s : State) : keyArg s = arg s 0 := (argument_word s 0).symm
 theorem output_argument (s : State) : scheduleArg s = arg s 2 := (argument_word s 2).symm
 theorem scratch_argument (s : State) : scratchArg s 4 = arg s 3 := (argument_word s 3).symm

theorem headPre_of_contract (s : State) (hs : contract.pre s) : HeadPre s := by
  obtain ⟨rd, wr, keyOut, keyScratch, outScratch, argsOut, argsScratch, _, _,
    valid, keyFit, outputFit, scratchFit, spFit⟩ := hs
  have bp : (preparedKey s).gpr .ebp = arg s 3 := by rw [preparedKey, gpr_setReg_self, scratch_argument]
  have sp : (preparedKey s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  have args (i : Nat) : arg (preparedKey s) i = arg s i := by unfold arg argAddr; rw [sp]; rfl
  have key : keyArg (preparedKey s) = arg s 0 := by rw [key_argument, args]
  have output : scheduleArg (preparedKey s) = arg s 2 := by rw [output_argument, args]
  have len : keyLength (preparedKey s) = (arg s 1).toNat := by unfold keyLength; rw [args]
  have argBase : argAddr (preparedKey s) 0 = argAddr s 0 := by unfold argAddr; rw [sp]
  have workSub : Region.Sub (workRegion (preparedKey s)) ⟨addr32 (arg s 3), 512⟩ := by
    rw [workRegion, bp]; exact Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (savedR s) ⟨addr32 (arg s 3), 512⟩ := by
    rw [savedR, scratch_argument]; exact Region.sub_prefix (by decide)
  have contains : ∀ i, 1 ≤ i → i ≤ 4 → (⟨argAddr s 0, 16⟩ : Region).Contains
      (wordAddr (s.gpr .esp) i) 4 := by
    intro i hlo hhi
    rw [wordAddr, addr_eq (by omega_using [spFit, hhi])]
    have h := argContainsCount s 4 spFit (i - 1) (by omega_using [hlo, hhi])
    rw [show 4 + 4 * (i - 1) = 4 * i by omega_using [hlo]] at h
    exact h
  have readArg : ∀ i, 1 ≤ i → i ≤ 4 → InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    intro i hlo hhi
    rw [rd, wr]
    exact ⟨⟨argAddr s 0, 16⟩, by simp, contains i hlo hhi⟩
  have slots : ∀ i < 128, InRegions (preparedKey s).wr (wordAddr ((preparedKey s).gpr .ebp) i) 4 := by
    intro i hi
    rw [bp, wordAddr, addr_eq (by omega_using [scratchFit, hi])]
    change InRegions s.wr _ 4
    rw [wr]
    exact ⟨⟨addr32 (arg s 3), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have ok : Ok sboxCfg (preparedKey s) := by
    refine ⟨slots, ?_, ?_, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · change ((preparedKey s).gpr .ebp).toNat + 512 ≤ 2 ^ 32; rw [bp]; exact scratchFit
    · intro k hk j hj; change j < 0 at hj; omega
  refine ⟨?_, ?_, readArg 4 (by decide) (by decide), readArg 2 (by decide) (by decide), ?_,
    argsScratch.sub_right saveSub, ?_, ?_⟩
  · refine ⟨ok, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro off ho
      rw [len] at ho
      rw [key]
      change InRegions (s.rd ++ s.wr) _ 4
      rw [rd, wr]
      exact ⟨⟨addr32 (arg s 0), (arg s 1).toNat⟩, by simp,
        Offset.contains_base _ ho (by omega_using [ho, keyFit])⟩
    · intro off ho
      rw [output]
      change InRegions s.wr _ 4
      rw [wr]
      exact ⟨⟨addr32 (arg s 2), 384⟩, by simp, Offset.contains_base _ ho (by omega_using [ho])⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      change InRegions (s.rd ++ s.wr) (wordAddr ((preparedKey s).gpr .esp) i) 4
      rw [sp]
      rcases hi with rfl | rfl
      · exact readArg 1 (by decide) (by decide)
      · exact readArg 3 (by decide) (by decide)
    · rw [argBase, outputR, output]; exact argsOut
    · rw [argBase]; exact argsScratch.sub_right workSub
    · rw [keyR, key, len, outputR, output]; exact keyOut
    · rw [keyR, key, len]; exact keyScratch.sub_right workSub
    · rw [outputR, output]; exact outScratch.sub_right workSub
    · rw [len]; exact valid
    · rw [key, len]; exact keyFit
    · rw [output]; exact outputFit
    · rw [sp]; exact spFit
  · rw [scratch_argument]; exact scratchFit
  · intro i hi
    rw [scratch_argument, wr]
    exact ⟨⟨addr32 (arg s 3), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [keyR, key_argument, keyLength, scratchR, scratch_argument]; exact keyScratch
  · rw [outputR, output_argument, scratchR, scratch_argument]; exact outScratch

end VG.Proof.TripleDes.X86.Key

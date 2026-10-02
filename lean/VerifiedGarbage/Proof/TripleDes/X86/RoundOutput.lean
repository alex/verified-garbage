import VerifiedGarbage.Proof.TripleDes.X86.RoundCheck
namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

theorem outputLiteral_eq : ∀ i < 8,
    outputLiterals.getD i (.block []) = .block (sboxOutputs i)
  | 0, _ => output0.lit_eq.symm
  | 1, _ => output1.lit_eq.symm
  | 2, _ => output2.lit_eq.symm
  | 3, _ => output3.lit_eq.symm
  | 4, _ => output4.lit_eq.symm
  | 5, _ => output5.lit_eq.symm
  | 6, _ => output6.lit_eq.symm
  | 7, _ => output7.lit_eq.symm
  | n + 8, h => by omega

def roundOutputs (s : State) (i : Nat) : BitVec 32 :=
  if i = 4 then s.gpr .esi
  else s.mem.readW (wordAddr (s.gpr .ebp) (16 + i)) 32

theorem roundOutput_ok (i : Nat) (hi : i < 8) (s : State) (hok : Ok outputCfg s) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      (∀ p < 32, (s'.gpr .esi).getLsbD p =
        xorBits (roundOutputs s) (outputBits i p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, ((sboxOutputs i).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) ∧ Frame [slotRegion outputCfg s] s.mem s'.mem := by
  have h := output_check i hi
  rw [outputLiteral_eq i hi] at h
  change check _ _ _ (sboxOutputs i) outputEnv (outputPost i) = true at h
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ h
  have hrel : Rel (LaneRel 8 (assign (roundOutputs s) 256)) outputCfg
      (fun _ => none) outputEnv s := by
    refine ⟨fun r a h => ?_, fun j a hj h => ?_, fun _ _ _ h => by cases h⟩
    · simp only [outputEnv] at h
      split at h
      · rename_i hr; subst r; cases h
        have hr := inWord_rel (roundOutputs s) (i := 4) (k := 8) (by decide)
        exact hr
      · cases h
    · simp only [outputEnv] at h
      split at h
      · rename_i hb; cases h
        have heq : 16 + (j - 16) = j := by omega
        have hne : j - 16 ≠ 4 := by omega
        have hr := inWord_rel (roundOutputs s) (i := j - 16) (k := 8) (by omega)
        simpa only [roundOutputs, hne, ite_false, heq, outputCfg] using hr
      · cases h
  obtain ⟨s', hs', post⟩ := run lanes_sound hok hrel he
  have ho := List.all_eq_true.mp hpost (.esi, outputBits i) (by simp)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at ho
  refine ⟨s', hs', ?_, post.rd, post.wr,
    fun r hr => post.other r (by simp [hr]), post.frame⟩
  exact outWord_rel (fun p hp a ha => ho.2 p hp a ha) (post.rel.reg .esi _ ho.1)
end VG.Proof.TripleDes.X86

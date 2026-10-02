import VerifiedGarbage.Proof.TripleDes.X86.RoundCheck
namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

theorem inputLiteral_eq : ∀ i < 8,
    inputLiterals.getD i (.block []) = .block (sboxInputBits i)
  | 0, _ => input0.lit_eq.symm
  | 1, _ => input1.lit_eq.symm
  | 2, _ => input2.lit_eq.symm
  | 3, _ => input3.lit_eq.symm
  | 4, _ => input4.lit_eq.symm
  | 5, _ => input5.lit_eq.symm
  | 6, _ => input6.lit_eq.symm
  | 7, _ => input7.lit_eq.symm
  | n + 8, h => by omega

theorem inputEnv_eq : inputEnv = linEnv [(.edi, 0)] := by
  unfold inputEnv linEnv
  congr 1
  funext r; cases r <;> rfl

def roundInputs (s : State) (i : Nat) : BitVec 32 :=
  if i = 0 then s.gpr .edi
  else s.mem.readW (wordAddr (s.gpr .edx) (i - 1)) 32

theorem roundInput_ok (i : Nat) (hi : i < 8) (s : State) (hok : Ok inputCfg s) :
    ∃ s', runBlock isa (sboxInputBits i) s = some s' ∧
      (∀ j < 6, ∀ p < 32,
        (s'.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD p =
          xorBits (roundInputs s) (inputBits i j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, ((sboxInputBits i).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) ∧ Frame [slotRegion inputCfg s] s.mem s'.mem := by
  have h := input_check i hi
  rw [inputLiteral_eq i hi] at h
  change check _ _ _ (sboxInputBits i) inputEnv (inputPost i) = true at h
  rw [inputEnv_eq] at h
  obtain ⟨s', run, out, rd, wr, keep, frame⟩ :=
    linear_slots_ok h hok (roundInputs s) (fun r k hk => by
      simp only [List.mem_singleton, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨by decide, rfl⟩) (fun j hj => by
        refine ⟨?_, ?_⟩
        · simp only [inputCfg] at hj; omega
        · simp only [inputCfg, roundInputs, Nat.add_eq_zero_iff, Nat.one_ne_zero,
            false_and, ite_false, Nat.add_sub_cancel_left])
  refine ⟨s', run, fun j hj p hp => ?_, rd, wr, keep, frame⟩
  exact out (16 + j) (inputBits i j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp
end VG.Proof.TripleDes.X86

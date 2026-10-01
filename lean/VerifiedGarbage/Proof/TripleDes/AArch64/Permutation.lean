import VerifiedGarbage.Proof.TripleDes.AArch64.Lit
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.Framework.AArch64.Linear

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.TripleDes.AArch64

def permutationCfg : Cfg := { base := .x2, slots := 0, ext := .x2, exts := 0 }
def permutationInputs (src : Reg) : List (Reg × Nat) := [(src, 0)]

def permutationBits {m : Nat} (positions : Vector Nat m) (n p : Nat) : List Nat :=
  if p < m then [n - positions.getD (m - 1 - p) 1] else []

def permutationOutputs {m : Nat} (positions : Vector Nat m) (n : Nat) (dst : Reg) :
    List (Reg × (Nat → List Nat)) := [(dst, permutationBits positions n)]

theorem initialPermutation_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs initialPermutation.lit)
      (linEnv (permutationInputs .x3)) (linPost 6 (permutationOutputs Spec.TripleDes.ip 64 .x10)) = true := by
  decide +kernel

theorem finalPermutation_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs finalPermutation.lit)
      (linEnv (permutationInputs .x3)) (linPost 6 (permutationOutputs Spec.TripleDes.fp 64 .x10)) = true := by
  decide +kernel

theorem keyPermutation1_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs keyPermutation1.lit)
      (linEnv (permutationInputs .x4)) (linPost 6 (permutationOutputs Spec.TripleDes.pc1 64 .x5)) = true := by
  decide +kernel

theorem keyPermutation2_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs keyPermutation2.lit)
      (linEnv (permutationInputs .x4)) (linPost 6 (permutationOutputs Spec.TripleDes.pc2 56 .x5)) = true := by
  decide +kernel

theorem permutationCfg_ok (s : State) : Ok permutationCfg s := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro k hk; simp [permutationCfg] at hk
  · intro k hk; simp [permutationCfg] at hk
  · intro k hk; simp [permutationCfg] at hk

theorem fixedPermutation_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (hn64 : n ≤ 64)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (src dst : Reg) (is : List Instr)
    (hchk : check (lanes 64 6) permutationCfg (linExt 1) is
      (linEnv (permutationInputs src)) (linPost 6 (permutationOutputs positions n dst)) = true)
    (s : State) :
    ∃ s', runBlock isa is s = some s' ∧
      s'.gpr dst = (Spec.TripleDes.permute positions ((s.gpr src).setWidth n)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, (is.all fun op => dstOf op != some r) = true → s'.gpr r = s.gpr r) := by
  let W : Nat → BitVec 64 := fun _ => s.gpr src
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ :=
    linear_ok hchk (permutationCfg_ok s) W (fun r i h => by
      simp only [permutationInputs, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, rfl⟩)
      (fun j hj => by simp [permutationCfg] at hj)
  refine ⟨s', hs', ?_, rd, wr, sp, ?_, keep⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hout := out dst (permutationBits positions n) (by simp [permutationOutputs]) j hj
    change (s'.gpr dst).getLsbD j =
      ((Spec.TripleDes.permute positions ((s.gpr src).setWidth n)).setWidth 64).getLsbD j
    rw [BitVec.getLsbD_setWidth]
    simp only [hj, decide_true, Bool.true_and]
    rw [hout]
    by_cases hjm : j < m
    · have hk : m - 1 - j < m := by omega
      obtain ⟨hlo, hhi⟩ := bounds _ hk
      have hsource : n - positions.getD (m - 1 - j) 1 < n := by omega
      have h64 : n - positions.getD (m - 1 - j) 1 < 64 := by omega
      rw [VG.Proof.TripleDes.permute_bit positions _ hn j hjm,
        BitVec.getLsbD_setWidth]
      simp only [hsource, decide_true, Bool.true_and, permutationBits, hjm, ite_true,
        xorBits, List.foldr_cons, List.foldr_nil, Bool.xor_false, bitOf,
        Nat.mod_eq_of_lt h64, W]
    · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
      simp only [permutationBits, hjm, ite_false, xorBits, List.foldr_nil]
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, permutationCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

end VG.Proof.TripleDes.AArch64

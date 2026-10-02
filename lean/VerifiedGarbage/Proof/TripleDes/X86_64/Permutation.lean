import VerifiedGarbage.Proof.TripleDes.X86_64.Lit
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.Framework.X86_64.Linear

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.TripleDes.X86_64

def permutationCfg : Cfg := { base := .rdx, slots := 0, ext := .rdx, exts := 0 }
def permutationInputs : List (Reg × Nat) := [(.rax, 0)]

def permutationBits {m : Nat} (positions : Vector Nat m) (n p : Nat) : List Nat :=
  if p < m then [n - positions.getD (m - 1 - p) 1] else []

def permutationOutputs {m : Nat} (positions : Vector Nat m) (n : Nat) :
    List (Reg × (Nat → List Nat)) := [(.rbx, permutationBits positions n)]

theorem initialPermutation_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs initialPermutation.lit)
      (linEnv permutationInputs) (linPost 6 (permutationOutputs Spec.TripleDes.ip 64)) = true := by
  decide +kernel

theorem finalPermutation_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs finalPermutation.lit)
      (linEnv permutationInputs) (linPost 6 (permutationOutputs Spec.TripleDes.fp 64)) = true := by
  decide +kernel

theorem keyPermutation1_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs keyPermutation1.lit)
      (linEnv permutationInputs) (linPost 6 (permutationOutputs Spec.TripleDes.pc1 64)) = true := by
  decide +kernel

theorem keyPermutation2_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs keyPermutation2.lit)
      (linEnv permutationInputs) (linPost 6 (permutationOutputs Spec.TripleDes.pc2 56)) = true := by
  decide +kernel

theorem permutationCfg_ok (s : State) : Ok permutationCfg s := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro k hk; simp [permutationCfg] at hk
  · intro k hk; simp [permutationCfg] at hk
  · intro k hk; simp [permutationCfg] at hk

theorem fixedPermutation_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (hn64 : n ≤ 64)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (is : List Instr)
    (hchk : check (lanes 64 6) permutationCfg (linExt 1) is
      (linEnv permutationInputs) (linPost 6 (permutationOutputs positions n)) = true)
    (s : State) :
    ∃ s', runBlock isa is s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute positions ((s.gpr .rax).setWidth n)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, (is.all fun op => op.dst != some r) = true → s'.gpr r = s.gpr r) := by
  let W : Nat → BitVec 64 := fun _ => s.gpr .rax
  obtain ⟨s', hs', out, rd, wr, keep, frame⟩ :=
    linear_ok hchk (permutationCfg_ok s) W (fun r i h => by
      simp only [permutationInputs, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, rfl⟩)
      (fun j hj => by simp [permutationCfg] at hj)
  refine ⟨s', hs', ?_, rd, wr, ?_, keep⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hout := out .rbx (permutationBits positions n) (by simp [permutationOutputs]) j hj
    change (s'.gpr .rbx).getLsbD j =
      ((Spec.TripleDes.permute positions ((s.gpr .rax).setWidth n)).setWidth 64).getLsbD j
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

end VG.Proof.TripleDes.X86_64

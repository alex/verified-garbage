import VerifiedGarbage.Proof.TripleDes.Arm.Lit
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.Framework.Arm.Linear

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.TripleDes.Arm

def permutationCfg : Cfg := { base := .r2, slots := 0, ext := .r2, exts := 0 }
def permutationInputs (lo hi : Reg) : List (Reg × Nat) := [(lo, 0), (hi, 1)]
def permutationBits {m : Nat} (positions : Vector Nat m) (n srcSplit dstSplit start p : Nat) : List Nat :=
  if p < dstSplit ∧ start + p < m then
    let source := n - positions.getD (m - 1 - (start + p)) 1
    [if source < srcSplit then source else 32 + source - srcSplit]
  else []
def permutationOutputs {m : Nat} (positions : Vector Nat m) (n srcSplit dstSplit : Nat) (lo hi : Reg) :
    List (Reg × (Nat → List Nat)) :=
  [(lo, permutationBits positions n srcSplit dstSplit 0),
   (hi, permutationBits positions n srcSplit (m - dstSplit) dstSplit)]

theorem initialPermutation_check :
    check (lanes 32 6) permutationCfg (linExt 2) (instrs initialPermutation.lit)
      (linEnv (permutationInputs .r5 .r4)) (linPost 6 (permutationOutputs Spec.TripleDes.ip 64 32 32 .r11 .r10)) = true := by
  decide +kernel

theorem finalPermutation_check :
    check (lanes 32 6) permutationCfg (linExt 2) (instrs finalPermutation.lit)
      (linEnv (permutationInputs .r11 .r10)) (linPost 6 (permutationOutputs Spec.TripleDes.fp 64 32 32 .r5 .r4)) = true := by
  decide +kernel

theorem keyPermutation1_check :
    check (lanes 32 6) permutationCfg (linExt 2) (instrs keyPermutation1.lit)
      (linEnv (permutationInputs .r5 .r4)) (linPost 6 (permutationOutputs Spec.TripleDes.pc1 64 32 28 .r11 .r10)) = true := by
  decide +kernel

theorem keyPermutation2_check :
    check (lanes 32 6) permutationCfg (linExt 2) (instrs keyPermutation2.lit)
      (linEnv (permutationInputs .r11 .r10)) (linPost 6 (permutationOutputs Spec.TripleDes.pc2 56 28 32 .r4 .r5)) = true := by
  decide +kernel

def packedInput (n split : Nat) (lo hi : BitVec 32) : BitVec n :=
  ((hi.setWidth (n - split)) ++ lo.setWidth split).setWidth n

theorem packedInput_bit (n split : Nat) (lo hi : BitVec 32) (k : Nat)
    (hk : k < n) (hs : split ≤ n) :
    (packedInput n split lo hi).getLsbD k =
      if k < split then lo.getLsbD k else hi.getLsbD (k - split) := by
  simp only [packedInput, BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : k < split
  · simp only [h, ite_true, decide_true, Bool.true_and]
  · have hb : k - split < n - split := by omega
    simp only [h, ite_false, hb, decide_true, Bool.true_and]

theorem permutationBits_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (split width start : Nat)
    (hs : split ≤ n) (hlo : split ≤ 32) (hhi : n - split ≤ 32)
    (hw : width + start ≤ m)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (lo hi : BitVec 32) (p : Nat) (hp : p < 32) :
    xorBits (fun i => if i = 0 then lo else hi)
      (permutationBits positions n split width start p) =
    (((Spec.TripleDes.permute positions (packedInput n split lo hi) >>> start).setWidth width).setWidth 32).getLsbD p := by
  simp only [BitVec.getLsbD_setWidth, hp, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight]
  by_cases hw' : p < width
  · have hm : start + p < m := by omega
    simp only [hw', decide_true, Bool.true_and]
    have hk : m - 1 - (start + p) < m := by omega
    obtain ⟨hb, ht⟩ := bounds _ hk
    have hn' : n - positions.getD (m - 1 - (start + p)) 1 < n := by omega
    rw [VG.Proof.TripleDes.permute_bit positions _ hn _ hm, packedInput_bit _ _ _ _ _ hn' hs]
    simp only [permutationBits, hw', hm, and_self, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false]
    let k := n - positions.getD (m - 1 - (start + p)) 1
    change bitOf (fun i => if i = 0 then lo else hi) (if k < split then k else 32 + k - split) =
      if k < split then lo.getLsbD k else hi.getLsbD (k - split)
    by_cases h : k < split
    · have h32 : k < 32 := by omega
      simp only [h, ite_true, bitOf, Nat.div_eq_of_lt h32, Nat.mod_eq_of_lt h32]
    · have h32 : k - split < 32 := by change n - positions.getD (m - 1 - (start + p)) 1 < n at hn'; dsimp [k]; omega
      have he : 32 + k - split = 32 * 1 + (k - split) := by omega
      simp only [h, ite_false, he, bitOf_word _ _ _ h32]
      rfl
  · simp only [hw', decide_false, Bool.false_and, permutationBits, false_and, ite_false, xorBits_nil]

theorem permutationCfg_ok (s : State) : Ok permutationCfg s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk; simp [permutationCfg] at hk
  · intro k hk; simp [permutationCfg] at hk
  · change (s.gpr .r2).toNat + 4 * 0 ≤ 2 ^ 32
    have h := (s.gpr .r2).isLt
    omega
  · intro k hk; simp [permutationCfg] at hk

theorem fixedPermutation_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (split dstSplit : Nat)
    (hs : split ≤ n) (hlo : split ≤ 32) (hhi : n - split ≤ 32) (hd : dstSplit ≤ m)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (srcLo srcHi dstLo dstHi : Reg) (is : List Instr)
    (hchk : check (lanes 32 6) permutationCfg (linExt 2) is
      (linEnv (permutationInputs srcLo srcHi))
      (linPost 6 (permutationOutputs positions n split dstSplit dstLo dstHi)) = true)
    (s : State) :
    ∃ s', runBlock isa is s = some s' ∧
      s'.gpr dstLo = ((Spec.TripleDes.permute positions
        (packedInput n split (s.gpr srcLo) (s.gpr srcHi))).setWidth dstSplit).setWidth 32 ∧
      s'.gpr dstHi = ((Spec.TripleDes.permute positions
        (packedInput n split (s.gpr srcLo) (s.gpr srcHi)) >>> dstSplit).setWidth (m - dstSplit)).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, (is.all fun op => dstOf op != some r) = true → s'.gpr r = s.gpr r) := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr srcLo else s.gpr srcHi
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ :=
    linear_ok hchk (permutationCfg_ok s) W (fun r i h => by
      simp only [permutationInputs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨by decide, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨by decide, rfl⟩)
      (fun j hj => by simp [permutationCfg] at hj)
  refine ⟨s', hs', ?_, ?_, rd, wr, sp, ?_, keep⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    have h := out dstLo (permutationBits positions n split dstSplit 0) (by simp [permutationOutputs]) p hp
    rw [h]
    have hbits := permutationBits_ok positions hn split dstSplit 0 hs hlo hhi (by omega) bounds (s.gpr srcLo) (s.gpr srcHi) p hp
    simpa only [BitVec.ushiftRight_zero] using hbits
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    have h := out dstHi (permutationBits positions n split (m - dstSplit) dstSplit)
      (by simp [permutationOutputs]) p hp
    rw [h]
    exact permutationBits_ok positions hn split (m - dstSplit) dstSplit hs hlo hhi
      (by omega) bounds _ _ p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, permutationCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

end VG.Proof.TripleDes.Arm

import VerifiedGarbage.Proof.CmacTripleDes.Block

/-!
# DES's key schedule, bit by bit

`expandDesKey` only moves the key's bits: bit `q` of round key `j` is bit
`rkSrc j q` of the key (`getLsbD_expandDesKey`), as the implementations
compute it. The proof follows `C` and `D` through the specification's loop
as maps of bit indices (`cIdx`), and compares the result with `rkSrc` by
`decide`.
-/

namespace VG.Proof.CmacTripleDes

open VG Spec.TripleDes Impl.CmacTripleDes

/-- Bit `i` of a 28-bit word rotated left by `r` is bit `rotIdx r i` of the word. -/
def rotIdx (r i : Nat) : Nat := (i + 28 - r % 28) % 28

theorem getLsbD_rotateLeft28 (x : BitVec 28) (r : Nat) {i : Nat} (hi : i < 28) :
    (x.rotateLeft r).getLsbD i = x.getLsbD (rotIdx r i) := by
  rw [BitVec.getLsbD_rotateLeft, rotIdx]
  have := Nat.mod_lt r (show 0 < 28 by decide)
  split
  · congr 1; omega
  · rw [decide_eq_true hi, Bool.true_and]; congr 1; omega

theorem rotIdx_lt (r i : Nat) : rotIdx r i < 28 := Nat.mod_lt _ (by decide)

/-- Bit `i` of `C` (or `D`) after `n` rotations is bit `cIdx n i` of the first. -/
def cIdx : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => cIdx n (rotIdx (rotations.getD n 0) i)

theorem cIdx_lt (n : Nat) {i : Nat} (hi : i < 28) : cIdx n i < 28 := by
  induction n generalizing i with
  | zero => exact hi
  | succ n ih => exact ih (Nat.mod_lt _ (by decide))

/-- Bit `q` of a round key, from `C` and `D` after the round's rotations. -/
def keyBit (c d : BitVec 28) (n q : Nat) : Bool :=
  let u := 56 - pc2.getD (47 - q) 1
  if u < 28 then d.getLsbD (cIdx n u) else c.getLsbD (cIdx n (u - 28))

/-- The loop of `expandDesKey`. -/
def ksStep (b : BitVec 28 × BitVec 28 × DesSchedule) (a : Nat) : BitVec 28 × BitVec 28 × DesSchedule :=
  (b.1.rotateLeft (rotations.getD a 0), b.2.1.rotateLeft (rotations.getD a 0),
    b.2.2.set! a (permute pc2 (b.1.rotateLeft (rotations.getD a 0) ++ b.2.1.rotateLeft (rotations.getD a 0))))

theorem pc2_u : ∀ q < 48, 56 - pc2.getD (47 - q) 1 < 56 := by decide

theorem ksFold (c₀ d₀ : BitVec 28) {n : Nat} (hn : n ≤ 16) :
    let st := (List.range n).foldl ksStep (c₀, d₀, Vector.replicate 16 0)
    (∀ i < 28, st.1.getLsbD i = c₀.getLsbD (cIdx n i)) ∧
    (∀ i < 28, st.2.1.getLsbD i = d₀.getLsbD (cIdx n i)) ∧
    ∀ j < n, ∀ q < 48, (st.2.2.getD j 0).getLsbD q = keyBit c₀ d₀ (j + 1) q := by
  induction n with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨hc, hd, hk⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun j hj q hq => ?_⟩
    · rw [ksStep, getLsbD_rotateLeft28 _ _ hi, hc _ (rotIdx_lt _ _), cIdx]
    · rw [ksStep, getLsbD_rotateLeft28 _ _ hi, hd _ (rotIdx_lt _ _), cIdx]
    · simp only [ksStep]
      rw [vgetD _ (by omega)]
      by_cases hjn : j = n
      · subst hjn
        rw [Vector.getElem_set!_self (by omega), getLsbD_permute _ _ (by decide) hq, BitVec.getLsbD_append,
          keyBit]
        have hu := pc2_u q hq
        rw [show 48 - 1 - q = 47 - q by omega]
        split
        · rename_i hu'
          rw [getLsbD_rotateLeft28 _ _ hu', hd _ (rotIdx_lt _ _)]
          rfl
        · rename_i hu'
          rw [getLsbD_rotateLeft28 _ _ (by omega), hc _ (rotIdx_lt _ _)]
          rfl
      · rw [Vector.getElem_set!_ne (by omega) (Ne.symm hjn), ← vgetD _ (by omega)]
        exact hk j (by omega) q hq

/-- `keyBit` from the key: the indices compose to `rkSrc`. -/
theorem keyBit_eq : ∀ j < 16, ∀ q < 48,
    (let u := 56 - pc2.getD (47 - q) 1
     if u < 28 then pc1Src (cIdx (j + 1) u) else pc1Src (28 + cIdx (j + 1) (u - 28))) = rkSrc j q := by
  decide

/-- Bit `q` of round key `j` is bit `rkSrc j q` of the key. -/
theorem getLsbD_expandDesKey (key : BitVec 64) {j q : Nat} (hj : j < 16) (hq : q < 48) :
    ((expandDesKey key).getD j 0).getLsbD q = key.getLsbD (rkSrc j q) := by
  have h : expandDesKey key = ((List.range 16).foldl ksStep
      ((permute pc1 key >>> 28).setWidth 28, (permute pc1 key).setWidth 28, Vector.replicate 16 0)).2.2 := by
    simp only [expandDesKey, Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
    rfl
  rw [h, (ksFold _ _ (Nat.le_refl 16)).2.2 j hj q hq, keyBit, ← keyBit_eq j hj q hq]
  have hu := pc2_u q hq
  split
  · rename_i hu'
    have hc := cIdx_lt (j + 1) hu'
    rw [BitVec.getLsbD_setWidth, decide_eq_true hc, Bool.true_and,
      getLsbD_permute _ _ (by decide) (by omega)]
    dsimp only
    rw [ite_eq_left hu']
    rfl
  · rename_i hu'
    have hc := cIdx_lt (j + 1) (show 56 - pc2.getD (47 - q) 1 - 28 < 28 by omega)
    rw [BitVec.getLsbD_setWidth, decide_eq_true hc, Bool.true_and, BitVec.getLsbD_ushiftRight,
      getLsbD_permute _ _ (by decide) (by omega)]
    dsimp only
    rw [ite_eq_right hu']
    rfl

end VG.Proof.CmacTripleDes

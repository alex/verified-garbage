import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA: `HintBitPack` and `HintBitUnpack` step by step, for every target

Untrusted: everything here is checked by Lean. The spec's `hintBitPack` and
`hintBitUnpack` (Algorithms 20 and 21) are nested `for` loops in `Id`, the
second with early returns. Here they are restated as folds of one step per
coefficient (`hintBitPack_eq`, `hintBitUnpack_eq`), which an implementation
follows iteration by iteration; and the index of `HintBitPack` is the number
of 1s before the current coefficient, at most the number of 1s of the hint
(`hpIdx_lt`), so it stays below `ω`.
-/

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa

/-- A `for` loop of `Id` whose body always continues is a fold. -/
theorem forIn_id_yield {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (hf : ∀ a b, f a b = pure (.yield (g b a))) : forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, hf, List.foldl_cons, ← ih]; rfl

/-! ## `HintBitPack` -/

/-- The default polynomial of `List.getD`. -/
abbrev noHint : Vector Bool n := Vector.replicate n false

/-- Coefficient `j` of the polynomial `hi`: if it is 1, `y[index] ← j` and the
index is incremented. -/
def hpStep (hi : Vector Bool n) (s : Array Byte × Nat) (j : Nat) : Array Byte × Nat :=
  if hi[j]! then (s.1.set! s.2 (BitVec.ofNat 8 j), s.2 + 1) else s

/-- Polynomial `i`: its coefficients, then `y[ω + i] ← index`. -/
def hpPoly (ω : Nat) (h : List (Vector Bool n)) (s : Array Byte × Nat) (i : Nat) : Array Byte × Nat :=
  let s' := (List.range n).foldl (hpStep (h.getD i noHint)) s
  (s'.1.set! (ω + i) (BitVec.ofNat 8 s'.2), s'.2)

theorem hintBitPack_eq (ω k : Nat) (h : List (Vector Bool n)) :
    hintBitPack ω k h = ((List.range k).foldl (hpPoly ω h) (Array.replicate (ω + k) 0, 0)).1.toList := by
  dsimp only [hintBitPack]
  rw [forIn_id_yield (List.range k) _ _ (hpPoly ω h) (fun i s => ?_)]
  · rfl
  · rw [forIn_id_yield (List.range n) _ _ (hpStep (h.getD i noHint)) (fun j s => ?_)]
    · rfl
    · simp only [hpStep]; split <;> rfl

/-- The number of 1s among the first `j` coefficients of `hi`. -/
def count (hi : Vector Bool n) (j : Nat) : Nat := ((List.range j).filter fun t => hi[t]!).length

theorem count_succ (hi : Vector Bool n) (j : Nat) : count hi (j + 1) = count hi j + (if hi[j]! then 1 else 0) := by
  simp only [count, List.range_succ, List.filter_append, List.length_append]
  split <;> simp_all

theorem count_mono (hi : Vector Bool n) {j j' : Nat} (h : j ≤ j') : count hi j ≤ count hi j' := by
  induction j' with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ j' ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [count_succ]; have := ih (by omega); omega
    · exact Nat.le_refl _

theorem count_n (hi : Vector Bool n) : count hi n = (hi.toList.filter id).length := by
  have e : hi.toList = (List.range n).map fun t => hi[t]! :=
    List.ext_getElem (by simp) fun t h₁ h₂ => by
      simp only [Vector.getElem_toList, List.getElem_map, List.getElem_range]
      rw [getElem!_pos hi t (by simpa using h₁)]
  rw [count, e, List.filter_map, List.length_map]
  rfl

theorem hpStep_idx (hi : Vector Bool n) (s : Array Byte × Nat) (j : Nat) :
    (hpStep hi s j).2 = s.2 + (if hi[j]! then 1 else 0) := by
  unfold hpStep; split <;> simp_all

/-- The index after the first `j` coefficients. -/
theorem hpSteps_idx (hi : Vector Bool n) (s : Array Byte × Nat) (j : Nat) :
    ((List.range j).foldl (hpStep hi) s).2 = s.2 + count hi j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, count_succ, hpStep_idx, ih]
    omega

theorem sum_range_mono (f : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    ((List.range a).map f).sum ≤ ((List.range b).map f).sum := by
  induction b with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [List.range_succ, List.map_append, List.sum_append]; have := ih (by omega); omega
    · exact Nat.le_refl _

theorem sum_range_succ (f : Nat → Nat) (a : Nat) :
    ((List.range (a + 1)).map f).sum = ((List.range a).map f).sum + f a := by
  rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero]

/-- The number of 1s before coefficient `j` of polynomial `i`. -/
def onesBefore (h : List (Vector Bool n)) (i j : Nat) : Nat :=
  ((List.range i).map fun t => count (h.getD t noHint) n).sum + count (h.getD i noHint) j

theorem hpPoly_idx (ω : Nat) (h : List (Vector Bool n)) (s : Array Byte × Nat) (i : Nat) :
    (hpPoly ω h s i).2 = s.2 + count (h.getD i noHint) n := by
  dsimp only [hpPoly]; exact hpSteps_idx _ s n

theorem hpPolys_idx (ω : Nat) (h : List (Vector Bool n)) (s : Array Byte × Nat) (i : Nat) :
    ((List.range i).foldl (hpPoly ω h) s).2 = s.2 + onesBefore h i 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hpPoly_idx, ih]
    unfold onesBefore
    rw [sum_range_succ]
    have : count (h.getD (i + 1) noHint) 0 = 0 := rfl
    have : count (h.getD i noHint) 0 = 0 := rfl
    omega

theorem hintOnes_eq {h : List (Vector Bool n)} {k : Nat} (hk : h.length = k) :
    hintOnes h = ((List.range k).map fun t => count (h.getD t noHint) n).sum := by
  subst hk
  unfold hintOnes
  congr 1
  refine List.ext_getElem (by simp) fun t h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, count_n]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₂), Option.getD_some]

/-- The index before a 1 is less than the number of 1s. -/
theorem hpIdx_lt {h : List (Vector Bool n)} {k i j : Nat} (hk : h.length = k) (hi : i < k) (hj : j < n)
    (h1 : (h.getD i noHint)[j]! = true) : onesBefore h i j < hintOnes h := by
  rw [hintOnes_eq hk]
  have hc : count (h.getD i noHint) j < count (h.getD i noHint) n := by
    have := count_mono (h.getD i noHint) (show j + 1 ≤ n by omega)
    rw [count_succ, h1] at this; simp only [ite_true] at this; omega
  have hs := sum_range_mono (fun t => count (h.getD t noHint) n) (show i + 1 ≤ k by omega)
  rw [sum_range_succ] at hs
  unfold onesBefore
  omega

/-- The index after polynomial `i` is at most the number of 1s. -/
theorem onesBefore_n_le {h : List (Vector Bool n)} {k i : Nat} (hk : h.length = k) (hi : i < k) :
    onesBefore h i n ≤ hintOnes h := by
  rw [hintOnes_eq hk]
  unfold onesBefore
  rw [← sum_range_succ (fun t => count (h.getD t noHint) n)]
  exact sum_range_mono _ (by omega)

end VG.Proof.MlDsa.Pack

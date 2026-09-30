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

/-! ## `HintBitUnpack` -/

theorem ite_pos' {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ite_neg' {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-- A fold that stops at the first failure. -/
def optFold {α S : Type} (g : S → α → Option S) : List α → S → Option S
  | [], st => some st
  | a :: l, st => (g st a).bind (optFold g l)

theorem forIn_opt {α S R : Type} (g : S → α → Option S) (r₀ : R)
    (f : α → Option R × S → Id (ForInStep (Option R × S)))
    (hf : ∀ a st, (g st a = none → ∃ st', f a (none, st) = pure (.done (some r₀, st'))) ∧
      (∀ st', g st a = some st' → f a (none, st) = pure (.yield (none, st')))) :
    ∀ (l : List α) (st : S), (optFold g l st = none ∧ ∃ st', forIn l (none, st) f = pure (some r₀, st')) ∨
      (∃ st', optFold g l st = some st' ∧ forIn l (none, st) f = pure (none, st'))
  | [], st => .inr ⟨st, rfl, rfl⟩
  | a :: l, st => by
    rw [List.forIn_cons]
    cases hg : g st a with
    | none =>
      obtain ⟨st', h⟩ := (hf a st).1 hg
      exact .inl ⟨by simp [optFold, hg], st', by rw [h]; rfl⟩
    | some st₁ =>
      rw [(hf a st).2 st₁ hg]
      rcases forIn_opt g r₀ f hf l st₁ with ⟨h1, st', h2⟩ | ⟨st', h1, h2⟩
      · exact .inl ⟨by simp [optFold, hg, h1], st', by rw [← h2]; rfl⟩
      · exact .inr ⟨st', by simp [optFold, hg, h1], by rw [← h2]; rfl⟩

/-- A `for` loop of `Id` that stops at the first failure, followed by `G`. -/
theorem forIn_opt_bind {α S R β : Type} (g : S → α → Option S) (r₀ : R)
    (f : α → Option R × S → Id (ForInStep (Option R × S)))
    (hf : ∀ a st, (g st a = none → ∃ st', f a (none, st) = pure (.done (some r₀, st'))) ∧
      (∀ st', g st a = some st' → f a (none, st) = pure (.yield (none, st'))))
    (l : List α) (st : S) (G : Option R × S → Id β) (rhs : β)
    (hn : optFold g l st = none → ∀ st', G (some r₀, st') = rhs)
    (hs : ∀ st', optFold g l st = some st' → G (none, st') = rhs) :
    (forIn l (none, st) f >>= G) = rhs := by
  rcases forIn_opt g r₀ f hf l st with ⟨h1, st', h2⟩ | ⟨st', h1, h2⟩
  · rw [h2]; exact hn h1 st'
  · rw [h2]; exact hs st' h1

/-- A `for` loop of `Id` that stops at the first failure, as the body of an
enclosing one. -/
theorem forIn_opt_step {α S R R' : Type} (g : S → α → Option S) (r₀ : R) (r₀' : R')
    (f : α → Option R × S → Id (ForInStep (Option R × S)))
    (hf : ∀ a st, (g st a = none → ∃ st', f a (none, st) = pure (.done (some r₀, st'))) ∧
      (∀ st', g st a = some st' → f a (none, st) = pure (.yield (none, st'))))
    (l : List α) (st : S) (G : Option R × S → Id (ForInStep (Option R' × S)))
    (hG₁ : ∀ st', G (some r₀, st') = pure (.done (some r₀', st'))) (hG₂ : ∀ st', G (none, st') = pure (.yield (none, st'))) :
    (optFold g l st = none → ∃ st', (forIn l (none, st) f >>= G) = pure (.done (some r₀', st'))) ∧
      (∀ st', optFold g l st = some st' → (forIn l (none, st) f >>= G) = pure (.yield (none, st'))) := by
  rcases forIn_opt g r₀ f hf l st with ⟨h1, st', h2⟩ | ⟨st', h1, h2⟩
  · refine ⟨fun _ => ⟨st', ?_⟩, fun _ h => ?_⟩
    · rw [h2]; exact hG₁ st'
    · rw [h1] at h; cases h
  · refine ⟨fun h => ?_, fun st'' h => ?_⟩
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h; rw [h2]; exact hG₂ st'

/-- Set coefficient `b` of polynomial `i`. -/
def huSet (i b : Nat) (h : Array (Vector Bool n)) : Array (Vector Bool n) :=
  h.set! i ((h.getD i noHint).set! b true)

/-- The index of polynomial `i` from `first`: its coefficient `y[index]`, after
checking it is greater than the previous one. -/
def huStep (y : Array Byte) (i first : Nat) (st : Array (Vector Bool n) × Nat) (_ : Nat) :
    Option (Array (Vector Bool n) × Nat) :=
  if st.2 > first ∧ (y.getD (st.2 - 1) 0).toNat ≥ (y.getD st.2 0).toNat then none
  else some (huSet i (y.getD st.2 0).toNat st.1, st.2 + 1)

/-- Polynomial `i`: the bound `y[ω + i]`, checked, and its coefficients. -/
def huPoly (ω : Nat) (y : Array Byte) (st : Array (Vector Bool n) × Nat) (i : Nat) :
    Option (Array (Vector Bool n) × Nat) :=
  let bound := (y.getD (ω + i) 0).toNat
  if bound < st.2 ∨ bound > ω then none else optFold (huStep y i st.2) (List.range (bound - st.2)) st

/-- The bytes after the last index are zero. -/
def huTrail (y : Array Byte) (_ : Unit) (i : Nat) : Option Unit := if y.getD i 0 ≠ 0 then none else some ()

theorem hintBitUnpack_eq (ω k : Nat) (y : List Byte) :
    hintBitUnpack ω k y =
      match optFold (huPoly ω y.toArray) (List.range k) (Array.replicate k noHint, 0) with
      | none => none
      | some (h, idx) => (optFold (huTrail y.toArray) (List.range' idx (ω - idx)) ()).map fun _ => h.toList := by
  dsimp only [hintBitUnpack]
  refine forIn_opt_bind (huPoly ω y.toArray) (none : Option (List (Vector Bool n))) _ (fun i st => ?_) _ _ _ _
    (fun h1 st' => by rw [h1]; rfl) (fun st' h1 => ?_)
  · -- A polynomial.
    obtain ⟨hh, idx⟩ := st
    dsimp only
    by_cases hc : (y.toArray.getD (ω + i) 0).toNat < idx ∨ (y.toArray.getD (ω + i) 0).toNat > ω
    · simp only [huPoly, hc, ↓reduceIte]
      exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => (by cases h)⟩
    · simp only [huPoly, hc, ↓reduceIte]
      refine forIn_opt_step (huStep y.toArray i idx) (none : Option (List (Vector Bool n))) none _
        (fun x st => ?_) _ _ _ (fun _ => rfl) (fun _ => rfl)
      obtain ⟨h2, idx2⟩ := st
      dsimp only
      simp only [huStep, huSet, noHint]
      by_cases e1 : idx2 > idx
      · by_cases e2 : (y.toArray.getD (idx2 - 1) 0).toNat ≥ (y.toArray.getD idx2 0).toNat
        · simp only [e1, e2, and_self, ↓reduceIte]
          exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => (by cases h)⟩
        · simp only [e1, e2, and_false, ↓reduceIte]
          exact ⟨fun h => (by cases h), fun st' h => (by cases h; rfl)⟩
      · simp only [e1, false_and, ↓reduceIte]
        exact ⟨fun h => (by cases h), fun st' h => (by cases h; rfl)⟩
  · -- The trailing bytes.
    obtain ⟨hh, idx⟩ := st'
    rw [h1]
    dsimp only
    refine forIn_opt_bind (huTrail y.toArray) (none : Option (List (Vector Bool n))) _ (fun i st => ?_) _ _ _ _
      (fun h2 _ => by rw [h2]; rfl) (fun st' h2 => by rw [h2]; rfl)
    rw [show huTrail y.toArray st i = if y.toArray.getD i 0 ≠ 0 then none else some () from rfl]
    by_cases hy : y.toArray.getD i 0 ≠ 0
    · rw [ite_pos' hy, ite_pos' hy]
      exact ⟨fun _ => ⟨(), rfl⟩, fun _ h => (by cases h)⟩
    · rw [ite_neg' hy, ite_neg' hy]
      exact ⟨fun h => (by cases h), fun st' h => (by cases h; rfl)⟩

theorem optFold_append {α S : Type} (g : S → α → Option S) (l₁ l₂ : List α) (st : S) :
    optFold g (l₁ ++ l₂) st = (optFold g l₁ st).bind (optFold g l₂) := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons a l ih =>
    simp only [List.cons_append, optFold]
    cases g st a with
    | none => rfl
    | some st' => exact ih st'

theorem optFold_range_succ {S : Type} (g : S → Nat → Option S) (m : Nat) (st : S) :
    optFold g (List.range (m + 1)) st = (optFold g (List.range m) st).bind fun st' => g st' m := by
  rw [List.range_succ, optFold_append]
  cases optFold g (List.range m) st with
  | none => rfl
  | some st' => simp only [Option.bind_some, optFold]; cases g st' m <;> rfl

theorem optFold_range'_succ {S : Type} (g : S → Nat → Option S) (a m : Nat) (st : S) :
    optFold g (List.range' a (m + 1)) st = (optFold g (List.range' a m) st).bind fun st' => g st' (a + m) := by
  rw [List.range'_concat, optFold_append]
  cases optFold g (List.range' a m) st with
  | none => rfl
  | some st' => simp only [Option.bind_some, optFold, Nat.one_mul]; cases g st' (a + m) <;> rfl

/-- Once a fold fails, it stays failed. -/
theorem optFold_range_none {S : Type} (g : S → Nat → Option S) {t m : Nat} (h : t ≤ m) {st : S}
    (hn : optFold g (List.range t) st = none) : optFold g (List.range m) st = none := by
  induction m with
  | zero => rw [Nat.le_zero.mp h] at hn; exact hn
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [optFold_range_succ, ih (by omega)]; rfl
    · exact hn

theorem optFold_range'_none {S : Type} (g : S → Nat → Option S) (a : Nat) {t m : Nat} (h : t ≤ m) {st : S}
    (hn : optFold g (List.range' a t) st = none) : optFold g (List.range' a m) st = none := by
  induction m with
  | zero => rw [Nat.le_zero.mp h] at hn; exact hn
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [optFold_range'_succ, ih (by omega)]; rfl
    · exact hn

theorem huSet_size (i b : Nat) (h : Array (Vector Bool n)) : (huSet i b h).size = h.size := by
  simp [huSet]

/-- Coefficient `j` of polynomial `i'` after setting coefficient `b` of
polynomial `i`. -/
theorem huSet_get {i b : Nat} {h : Array (Vector Bool n)} (hi : i < h.size) {i' j : Nat}
    (hj : j < n) :
    ((huSet i b h).getD i' noHint)[j]! = if i' = i ∧ j = b then true else (h.getD i' noHint)[j]! := by
  simp only [huSet, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases e : i = i'
  · subst e
    simp only [ite_true, hi, Option.getD_some]
    rw [getElem!_pos _ j hj, getElem!_pos _ j hj, Vector.set!_eq_setIfInBounds, Vector.getElem_setIfInBounds]
    by_cases e2 : b = j
    · subst e2; simp
    · simp [e2, Ne.symm e2]
  · simp [e, Ne.symm e]

end VG.Proof.MlDsa.Pack


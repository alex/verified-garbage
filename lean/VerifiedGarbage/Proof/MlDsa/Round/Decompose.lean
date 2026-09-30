import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA: `Decompose` and `Power2Round` by multiplications and shifts, for every target

Untrusted: everything here is checked by Lean. The rounding functions of
FIPS 204 §7.4 in the form an implementation computes them, for every
coefficient `a < q`:

* `Power2Round(a)` is `(⌊(a + 4095) / 2¹³⌋, ((a + 4095) mod 2¹³) - 4095)`
  (`power2Round_eq`);
* `Decompose(a)`, for `γ₂` in `gamma2s`: its `r₁` is `f mod m`, for
  `f = ⌊(a + γ₂ - 1) / (2γ₂)⌋` (`hbF`, at most `m`) and `m = (q - 1)/(2γ₂)`
  (`hbM`: 16 or 44); its `r₀` is `a - r₁ · 2γ₂`, but `a - q` when `f = m`
  (`decompose_eq`);
* `f` without a division (`hbF_eq`), as the reference implementation
  computes it: `b = ⌊(a + 127)/2⁷⌋`, then `⌊(1025 b + 2²¹)/2²²⌋` for
  `γ₂ = (q - 1)/32` and `⌊(11275 b + 2²³)/2²⁴⌋` for `γ₂ = (q - 1)/88`
  (`hbMul`, `hbAdd`, `hbShift`). It is proven for every `a < q` from the
  bounds of the quotient and remainder of `b + c` by `2γ₂/2⁷` (`hbF_mulShift`),
  which `omega` checks for both values of `γ₂`, not by enumerating `a`.
-/

namespace VG.Proof.MlDsa.Round

open VG.Spec.MlDsa

theorem q_eq : q = 8380417 := rfl

theorem mem_gamma2s {γ₂ : Nat} (h : γ₂ ∈ gamma2s) : γ₂ = 95232 ∨ γ₂ = 261888 := by
  simpa [gamma2s] using h

/-! ## `Decompose` -/

/-- `m = (q - 1)/(2γ₂)`, the number of values of `r₁`. -/
def hbM (γ₂ : Nat) : Nat := (q - 1) / (2 * γ₂)

/-- `⌊(a + γ₂ - 1)/(2γ₂)⌋`: `r₁` of `Decompose(a)` before it is reduced modulo `m`. -/
def hbF (γ₂ a : Nat) : Nat := (a + γ₂ - 1) / (2 * γ₂)

theorem hbM_32 : hbM 261888 = 16 := rfl
theorem hbM_88 : hbM 95232 = 44 := rfl

theorem hbF_le {γ₂ : Nat} (h : γ₂ ∈ gamma2s) {a : Nat} (ha : a < q) : hbF γ₂ a ≤ hbM γ₂ := by
  rcases mem_gamma2s h with rfl | rfl <;> simp only [hbF, hbM, q_eq] at * <;> omega

theorem hbM_mul {γ₂ : Nat} (h : γ₂ ∈ gamma2s) : hbM γ₂ * (2 * γ₂) = q - 1 := by
  rcases mem_gamma2s h with rfl | rfl <;> rfl

/-- `Decompose(a)`: `(f mod m, a - (f mod m) · 2γ₂)`, less `q` when `f = m`. -/
theorem decompose_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) :
    decompose γ₂ r = (((hbF γ₂ r.val % hbM γ₂ : Nat) : Int),
      (r.val : Int) - ((hbF γ₂ r.val % hbM γ₂ * (2 * γ₂) : Nat) : Int) -
        (if hbF γ₂ r.val = hbM γ₂ then (q : Int) else 0)) := by
  have hr := r.isLt
  by_cases hc : hbF γ₂ r.val = hbM γ₂
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    rcases mem_gamma2s h with rfl | rfl <;>
    · simp only [decompose, modPm, hbF, hbM, q_eq] at *
      split <;> split <;> simp only [Prod.mk.injEq] <;> omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    rcases mem_gamma2s h with rfl | rfl <;>
    · simp only [decompose, modPm, hbF, hbM, q_eq] at *
      split <;> split <;> simp only [Prod.mk.injEq] <;> omega

theorem highBits_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) :
    highBits γ₂ r = ((hbF γ₂ r.val % hbM γ₂ : Nat) : Int) := by
  rw [highBits, decompose_eq h]

theorem lowBits_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) :
    lowBits γ₂ r = (r.val : Int) - ((hbF γ₂ r.val % hbM γ₂ * (2 * γ₂) : Nat) : Int) -
      (if hbF γ₂ r.val = hbM γ₂ then (q : Int) else 0) := by
  rw [lowBits, decompose_eq h]

/-! ## `f` by a multiplication and shifts -/

/-- The multiplier. -/
def hbMul (γ₂ : Nat) : Nat := if γ₂ = 261888 then 1025 else 11275

/-- The shift. -/
def hbShift (γ₂ : Nat) : Nat := if γ₂ = 261888 then 22 else 24

/-- Half of `2 ^ hbShift`, which rounds the quotient. -/
def hbAdd (γ₂ : Nat) : Nat := if γ₂ = 261888 then 2 ^ 21 else 2 ^ 23

/-- `f` as the reference implementation computes it. -/
theorem hbF_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) {a : Nat} (ha : a < q) :
    hbF γ₂ a = ((a + 127) / 128 * hbMul γ₂ + hbAdd γ₂) / 2 ^ hbShift γ₂ := by
  rw [q_eq] at ha
  rcases mem_gamma2s h with rfl | rfl
  · show (a + 95232 - 1) / (2 * 95232) = ((a + 127) / 128 * 11275 + 2 ^ 23) / 2 ^ 24
    omega
  · show (a + 261888 - 1) / (2 * 261888) = ((a + 127) / 128 * 1025 + 2 ^ 21) / 2 ^ 22
    omega

/-! ## `ℤ_q` -/

theorem ofInt_val (x : Int) : (ofInt x).val = (x % (q : Int)).toNat % q := rfl

/-- `ofInt (a - x)` for `x ≤ q`, as a conditional addition of `q` computes it. -/
theorem ofInt_sub_val {a x : Nat} (ha : a < q) (hx : x ≤ q) (c : Int) :
    (ofInt ((a : Int) - (x : Int) - c * (q : Int))).val = if a < x then a + q - x else a - x := by
  rw [ofInt_val, q_eq] at *
  split <;> omega

theorem val_add (a b : Zq) : (a + b).val = (a.val + b.val) % q := Fin.val_add a b

/-! ## `LowBits` -/

/-- `LowBits(a)` modulo `q`: `a - r₁ · 2γ₂` plus `q` if it is negative. -/
theorem lowBits_val {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) :
    (ofInt (lowBits γ₂ r)).val =
      if r.val < hbF γ₂ r.val % hbM γ₂ * (2 * γ₂) then r.val + q - hbF γ₂ r.val % hbM γ₂ * (2 * γ₂)
      else r.val - hbF γ₂ r.val % hbM γ₂ * (2 * γ₂) := by
  have hx : hbF γ₂ r.val % hbM γ₂ * (2 * γ₂) ≤ q := by
    have := hbM_mul h
    have : hbF γ₂ r.val % hbM γ₂ < hbM γ₂ := Nat.mod_lt _ (by rcases mem_gamma2s h with rfl | rfl <;> decide)
    have := Nat.mul_le_mul_right (2 * γ₂) (Nat.le_of_lt this)
    omega
  rw [lowBits_eq h, ← ofInt_sub_val r.isLt hx (if hbF γ₂ r.val = hbM γ₂ then 1 else 0)]
  congr 2
  split <;> simp

/-! ## `Power2Round` -/

theorem power2Round_eq (r : Zq) :
    power2Round r = ((((r.val + 4095) / 8192 : Nat) : Int), (((r.val + 4095) % 8192 : Nat) : Int) - 4095) := by
  have := r.isLt
  simp only [power2Round, modPm, d, q_eq] at *
  split <;> simp only [Prod.mk.injEq] <;> omega

theorem power2Round_t0 (r : Zq) :
    (ofInt (power2Round r).2).val =
      if (r.val + 4095) % 8192 < 4095 then (r.val + 4095) % 8192 + q - 4095 else (r.val + 4095) % 8192 - 4095 := by
  rw [power2Round_eq]
  have := ofInt_sub_val (a := (r.val + 4095) % 8192) (x := 4095)
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)) (by decide) 0
  rw [← this, Int.zero_mul, Int.sub_zero]
  rfl

/-! ## `UseHint` and `MakeHint` -/

/-- `UseHint(h, a)`: `(f + m + δ) mod m` for `δ` 0 if not `h`, and else 1 if
`r₀ > 0`, that is `f · 2γ₂ < a`, and -1 otherwise. -/
theorem useHint_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (b : Bool) (r : Zq) :
    useHint γ₂ b r = (((if b then (if hbF γ₂ r.val * (2 * γ₂) < r.val then hbF γ₂ r.val + hbM γ₂ + 1
      else hbF γ₂ r.val + hbM γ₂ - 1) else hbF γ₂ r.val + hbM γ₂) % hbM γ₂ : Nat) : Int) := by
  have hr := r.isLt
  have hf := hbF_le h hr
  unfold useHint
  rw [decompose_eq h]
  dsimp only
  generalize r.val = a at hr hf ⊢
  generalize hbF γ₂ a = f at hf ⊢
  have hm : (q - 1) / (2 * γ₂) = hbM γ₂ := rfl
  rw [hm]
  rw [q_eq] at hr
  have hq : ((q : Nat) : Int) = 8380417 := rfl
  rw [hq]
  rcases mem_gamma2s h with rfl | rfl
  all_goals first | rw [hbM_88] at hf ⊢ | rw [hbM_32] at hf ⊢
  all_goals cases b <;> simp only [Bool.false_eq_true, false_and, ↓reduceIte, true_and]
  all_goals first | omega | (repeat' split) <;> omega

/-- `MakeHint(z, r)`: whether the `f mod m` of `r` and of `r + z` differ. -/
theorem makeHint_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (z r : Zq) :
    makeHint γ₂ z r = decide (hbF γ₂ r.val % hbM γ₂ ≠ hbF γ₂ ((r.val + z.val) % q) % hbM γ₂) := by
  unfold makeHint
  rw [highBits_eq h, highBits_eq h, val_add]
  simp only [ne_eq, Int.natCast_inj]

/-! ## Norms -/

/-- `‖a‖∞ < B` for `a ∈ ℤ_q`: `a < B` or `q - a < B`. -/
theorem normZq_lt (a : Zq) (B : Nat) : normZq a < B ↔ a.val < B ∨ q - a.val < B := by
  have := a.isLt
  simp only [normZq, modPm, q_eq] at *
  split <;> omega

theorem foldl_max_lt (L : List Nat) (a B : Nat) : L.foldl max a < B ↔ a < B ∧ ∀ x ∈ L, x < B := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih, Nat.max_lt]
    simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

/-- `‖f‖∞ < B` for `f ∈ R_q`: each coefficient's is. -/
theorem normRq_lt (f : Poly) (B : Nat) : normRq [f] < B ↔ ∀ i < n, normZq f[i]! < B := by
  simp only [normRq, List.flatMap_cons, List.flatMap_nil, List.append_nil, foldl_max_lt,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Vector.mem_toList_iff]
  constructor
  · intro ⟨_, h⟩ i hi
    rw [getElem!_pos f i hi]
    exact h _ (Vector.getElem_mem hi)
  · intro h
    refine ⟨?_, fun x hx => ?_⟩
    · have := h 0 (by decide); omega
    · obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp hx
      have := h i hi
      rwa [getElem!_pos f i hi] at this

end VG.Proof.MlDsa.Round

import VerifiedGarbage.Proof.MlDsa.Verify.Spec
import VerifiedGarbage.Spec.MlDsa.Poly
import Mathlib.Tactic.SplitIfs

/-!
# ML-DSA: the norm of `z` and the range of `UseHint`

Untrusted: everything here is checked by Lean. The coefficients of `z`
unpacked from a signature are in `(-γ₁, γ₁]` (`bitUnpack_bounds`), so the
norm of each, as a polynomial of `R_q` (what `vg_mldsa_norm_lt` computes),
is its norm in `R` (`normZq_ofInt`), and `‖z‖∞ < B` exactly when each
`‖z[i]‖∞ < B` (`normR_vZ_iff`). `UseHint` gives a coefficient of `w₁` of at
most `(q - 1)/(2γ₂) - 1` (`useHint_le`), which `SimpleBitPack` needs.
-/

namespace VG.Proof.MlDsa.Verify

open VG.Spec.MlDsa

/-! ## Norms -/

theorem foldl_max_lt {B : Nat} : ∀ (l : List Nat) (a : Nat), l.foldl max a < B ↔ a < B ∧ ∀ x ∈ l, x < B
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_max_lt l (max a x)]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · intro ⟨h₁, h₂⟩; exact ⟨by omega, by omega, h₂⟩
    · intro ⟨h₁, h₂, h₃⟩; exact ⟨by omega, h₃⟩

theorem normR_lt_iff {B : Nat} (hB : 0 < B) (zs : List IPoly) :
    normR zs < B ↔ ∀ z ∈ zs, ∀ x ∈ z.toList, x.natAbs < B := by
  unfold normR
  rw [foldl_max_lt]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · intro ⟨_, h⟩ z hz x hx; exact h _ ⟨z, hz, x, hx, rfl⟩
  · intro h; exact ⟨hB, fun _ ⟨z, hz, x, hx, e⟩ => e ▸ h z hz x hx⟩

theorem normRq_lt_iff {B : Nat} (hB : 0 < B) (f : Poly) :
    normRq [f] < B ↔ ∀ x ∈ f.toList, normZq x < B := by
  unfold normRq
  rw [foldl_max_lt]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map]
  constructor
  · intro ⟨_, h⟩ x hx; exact h _ ⟨x, hx, rfl⟩
  · intro h; exact ⟨hB, fun _ ⟨x, hx, e⟩ => e ▸ h x hx⟩

/-- `‖x mod q‖∞ = |x|` for `|x| ≤ (q - 1)/2`. -/
theorem normZq_ofInt {x : Int} (h₁ : -4190208 ≤ x) (h₂ : x ≤ 4190208) : normZq (ofInt x) = x.natAbs := by
  have hq : (q : Int) = 8380417 := rfl
  have hq2 : ((q / 2 : Nat) : Int) = 4190208 := rfl
  unfold normZq ofInt modPm
  have hv : ((Fin.ofNat q (x % (q : Int)).toNat : Zq).val : Int) = x % 8380417 := by
    rw [Fin.val_ofNat, hq, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hv]
  dsimp only
  rw [hq, hq2]
  split <;> omega

theorem bitsToInteger_lt : ∀ (l : List Bool), bitsToInteger l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have := bitsToInteger_lt l
    have : b.toNat ≤ 1 := by cases b <;> decide
    simp only [bitsToInteger, List.foldr_cons, List.length_cons, Nat.pow_succ] at *
    omega

/-- The coefficients of `BitUnpack(v, a, b)` are in `(b - 2^bitlen (a + b), b]`. -/
theorem bitUnpack_bounds (v : List Byte) (a b : Nat) {i : Nat} (hi : i < n) :
    (b : Int) - 2 ^ bitlen (a + b) < (bitUnpack v a b)[i] ∧ (bitUnpack v a b)[i] ≤ b := by
  simp only [bitUnpack, Vector.getElem_ofFn]
  have := bitsToInteger_lt ((List.range (bitlen (a + b))).map fun j =>
    (bytesToBits v).getD (i * bitlen (a + b) + j) false)
  rw [List.length_map, List.length_range] at this
  have e : ((2 ^ bitlen (a + b) : Nat) : Int) = 2 ^ bitlen (a + b) := Int.natCast_pow 2 _
  constructor <;> omega

/-- The parameter sets' `γ₁`. -/
def gamma1s : List Nat := [2 ^ 17, 2 ^ 19]

theorem bitlen_gamma1 {γ₁ : Nat} (h : γ₁ ∈ gamma1s) : (2 : Int) ^ bitlen (γ₁ - 1 + γ₁) = 2 * (γ₁ : Int) := by
  simp only [gamma1s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

/-- `‖z[i]‖∞` in `R_q` is its norm in `R`. -/
theorem normRq_vZ {B : Nat} (hB : 0 < B) (p : Params) (hg : p.γ₁ ∈ gamma1s) (σ : List Byte) (i : Nat) :
    normRq [toRq (vZ p σ i)] < B ↔ ∀ x ∈ (vZ p σ i).toList, x.natAbs < B := by
  rw [normRq_lt_iff hB]
  have hb := bitlen_gamma1 hg
  have hs : p.γ₁ ≤ 2 ^ 19 := by
    simp only [gamma1s, List.mem_cons, List.not_mem_nil, or_false] at hg; omega
  constructor
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [Vector.length_toList] at hj
    have hb' := bitUnpack_bounds (((σ.drop (p.ctildeLen + lenZ p * i)).take (lenZ p))) (p.γ₁ - 1) p.γ₁ hj
    rw [hb] at hb'
    have := h (toRq (vZ p σ i))[j] (List.mem_iff_getElem.mpr ⟨j, by simpa using hj, by simp⟩)
    simp only [toRq, Vector.getElem_map, Vector.getElem_toList] at this ⊢
    rw [normZq_ofInt (by unfold vZ; omega) (by unfold vZ; omega)] at this
    exact this
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [Vector.length_toList] at hj
    have hb' := bitUnpack_bounds (((σ.drop (p.ctildeLen + lenZ p * i)).take (lenZ p))) (p.γ₁ - 1) p.γ₁ hj
    rw [hb] at hb'
    simp only [toRq, Vector.getElem_toList, Vector.getElem_map]
    rw [normZq_ofInt (by unfold vZ; omega) (by unfold vZ; omega)]
    exact h _ (List.mem_iff_getElem.mpr ⟨j, by simpa using hj, by simp⟩)

/-- `‖z‖∞ < B` exactly when each `‖z[i]‖∞ < B`, in `R_q`. -/
theorem normR_vZ_iff {B : Nat} (hB : 0 < B) (p : Params) (hg : p.γ₁ ∈ gamma1s) (σ : List Byte) :
    normR ((List.range p.ℓ).map (vZ p σ)) < B ↔ ∀ i < p.ℓ, normRq [toRq (vZ p σ i)] < B := by
  rw [normR_lt_iff hB]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun i _ => (normRq_vZ hB p hg σ i).symm

/-! ## `UseHint` -/

/-- The coefficients of `w₁`: at most `(q - 1)/(2γ₂) - 1`. -/
theorem useHint_le₁ (h : Bool) (r : Zq) : (useHint ((q - 1) / 88) h r).toNat ≤ (q - 1) / (2 * ((q - 1) / 88)) - 1 := by
  have hr := r.isLt
  have e1 : (((q - 1) / (2 * ((q - 1) / 88)) : Nat) : Int) = 44 := rfl
  have e2 : ((2 * ((q - 1) / 88) : Nat) : Int) = 190464 := rfl
  have e3 : ((q : Nat) : Int) = 8380417 := rfl
  have e4 : ((2 * ((q - 1) / 88) / 2 : Nat) : Int) = 95232 := rfl
  have e5 : (q - 1) / (2 * ((q - 1) / 88)) - 1 = 43 := rfl
  unfold useHint decompose modPm
  have hR : 0 ≤ ((r.val : Nat) : Int) ∧ ((r.val : Nat) : Int) < 8380417 := ⟨by omega, by omega⟩
  simp only [e1, e2, e3, e4, e5]
  generalize ((r.val : Nat) : Int) = R at *
  split_ifs <;> omega

theorem useHint_le₂ (h : Bool) (r : Zq) : (useHint ((q - 1) / 32) h r).toNat ≤ (q - 1) / (2 * ((q - 1) / 32)) - 1 := by
  have hr := r.isLt
  have e1 : (((q - 1) / (2 * ((q - 1) / 32)) : Nat) : Int) = 16 := rfl
  have e2 : ((2 * ((q - 1) / 32) : Nat) : Int) = 523776 := rfl
  have e3 : ((q : Nat) : Int) = 8380417 := rfl
  have e4 : ((2 * ((q - 1) / 32) / 2 : Nat) : Int) = 261888 := rfl
  have e5 : (q - 1) / (2 * ((q - 1) / 32)) - 1 = 15 := rfl
  unfold useHint decompose modPm
  have hR : 0 ≤ ((r.val : Nat) : Int) ∧ ((r.val : Nat) : Int) < 8380417 := ⟨by omega, by omega⟩
  simp only [e1, e2, e3, e4, e5]
  generalize ((r.val : Nat) : Int) = R at *
  split_ifs <;> omega

/-- The coefficients of `w₁`: at most `(q - 1)/(2γ₂) - 1`. -/
theorem useHint_le {γ₂ : Nat} (hg : γ₂ ∈ gamma2s) (h : Bool) (r : Zq) :
    (useHint γ₂ h r).toNat ≤ (q - 1) / (2 * γ₂) - 1 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  exacts [useHint_le₁ h r, useHint_le₂ h r]

end VG.Proof.MlDsa.Verify

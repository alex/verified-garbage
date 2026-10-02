import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA: the coefficients of `BitPack` and `BitUnpack` modulo `q`, for every target

`BitPack(f mod± q, a, b)` packs `b - (x mod± q)` for each reduced coefficient
`x` of `f`, and `BitUnpack` gives `b - y` for each field `y`, cast to `ℤ_q`.
Both are `(b + q - x) mod q`, which an implementation computes without
branches as `b - x`, plus `q` if that borrows (`sub_modPm`, `ofInt_sub`).
-/

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa

/-- `b - (x mod± q)` for a reduced `x` whose `x mod± q` is at most
`b ≤ q/2`: `(b + q - x) mod q`. -/
theorem sub_modPm {x b : Nat} (hx : x < q) (hb : b ≤ q / 2) (hle : modPm x q ≤ b) :
    ((b : Int) - modPm x q).toNat = (b + q - x) % q := by
  have hq : q = 8380417 := rfl
  unfold modPm at hle ⊢
  simp only [hq] at hx hb hle ⊢
  split at hle <;> rename_i h <;> simp only [h, ite_true, ite_false] <;> omega

/-- The value `BitPack` packs is at most `a + b`. -/
theorem sub_modPm_le {x a b : Nat} (h₁ : -(a : Int) ≤ modPm x q) (h₂ : modPm x q ≤ b) :
    ((b : Int) - modPm x q).toNat ≤ a + b := by omega

/-- `b - y` in `ℤ_q`, for `b, y < q`: `(b + q - y) mod q`. -/
theorem ofInt_sub {b y : Nat} (hy : y < q) : (ofInt ((b : Int) - (y : Nat))).val = (b + q - y) % q := by
  simp only [ofInt, Fin.val_ofNat]
  rw [show ((b : Int) - (y : Nat)) % (q : Nat) = (((b + q - y : Nat) % q : Nat) : Int) by
    rw [Int.natCast_emod, show ((b + q - y : Nat) : Int) = (b : Int) - y + q by omega, Int.add_emod_right]]
  rw [Int.toNat_natCast, Nat.mod_mod]

/-- `c · 2ᵈ` in `ℤ_q`, for `c < 2¹⁰`: itself. -/
theorem ofInt_t1 {c : Nat} (hc : c < 2 ^ 10) : (ofInt (c * 2 ^ d : Nat)).val = c * 2 ^ 13 := by
  have hq : q = 8380417 := rfl
  have h : c * 2 ^ 13 < 2 ^ 23 := by omega
  simp only [ofInt, Fin.val_ofNat, d]
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.MlDsa.Pack

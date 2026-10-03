import VerifiedGarbage.Proof.X448.Wide.Word

/-!
# Two-word accumulators modulo 2¹²⁸

Untrusted: everything here is checked by Lean. A pair of words added to or
subtracted from another pair, with the carry, is the sum or difference
modulo `2 ^ 128`. A product's coefficient can be accumulated with
subtractions as well as additions this way: it is exact once the true value
is known to be in `[0, 2 ^ 128)`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.X448.Wide (pair)
open VG.Proof.Ed25519.AArch64 (mulHi mul_lo_hi)

abbrev M : Nat := 2 ^ 128

theorem pair_lt (lo hi : BitVec 64) : pair lo hi < M := by
  have := lo.isLt; have := hi.isLt
  simp only [pair, M]
  omega

theorem addPair_mod (lo hi a b : BitVec 64) :
    pair (addCarry lo a false) (addCarry hi b (carryOut lo a false)) = (pair lo hi + pair a b) % M := by
  have e0 := addCarry_value lo a false
  have e1 := addCarry_value hi b (carryOut lo a false)
  have h := pair_lt (addCarry lo a false) (addCarry hi b (carryOut lo a false))
  have hc := Bool.toNat_le (carryOut hi b (carryOut lo a false))
  simp only [Bool.toNat_false, Nat.add_zero] at e0
  simp only [pair, M] at h ⊢
  omega

theorem subPair_mod (lo hi a b : BitVec 64) :
    pair (addCarry lo (~~~a) true) (addCarry hi (~~~b) (carryOut lo (~~~a) true)) =
      (pair lo hi + (M - pair a b)) % M := by
  have e0 := addCarry_value lo (~~~a) true
  have e1 := addCarry_value hi (~~~b) (carryOut lo (~~~a) true)
  have h := pair_lt (addCarry lo (~~~a) true) (addCarry hi (~~~b) (carryOut lo (~~~a) true))
  have hc := Bool.toNat_le (carryOut hi (~~~b) (carryOut lo (~~~a) true))
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.toNat_not, Bool.toNat_true] at e0 e1
  simp only [pair, M] at h ⊢
  omega

theorem mulPair (a b : BitVec 64) : pair (a * b) (mulHi a b) = a.toNat * b.toNat := by
  have := mul_lo_hi a b
  simp only [pair]
  omega

/-- Adding to an accumulator, as integers modulo `2 ^ 128`. -/
theorem add_emod {x : Nat} {e : Int} (h : (x : Int) = e % M) (p : Nat) :
    (((x + p) % M : Nat) : Int) = (e + p) % M := by
  rw [Int.natCast_emod, Int.natCast_add, h, Int.emod_add_emod]

/-- Subtracting from an accumulator, as integers modulo `2 ^ 128`. -/
theorem sub_emod {x : Nat} {e : Int} (h : (x : Int) = e % M) {p : Nat} (hp : p ≤ M) :
    (((x + (M - p)) % M : Nat) : Int) = (e - p) % M := by
  rw [Int.natCast_emod, Int.natCast_add, Int.natCast_sub hp, h, Int.emod_add_emod,
    show e + ((M : Nat) - (p : Int)) = e - p + (M : Nat) by omega, Int.add_emod_right]

/-- An accumulator holds its true value once that is known to fit. -/
theorem exact_of_emod {x : Nat} {e : Int} (h : (x : Int) = e % M) {v : Nat} (hv : e = v)
    (hlt : v < M) : x = v := by
  rw [hv, ← Int.natCast_emod, Nat.mod_eq_of_lt hlt] at h
  exact Int.ofNat.inj h

end VG.Proof.Curve448.AArch64.Fast

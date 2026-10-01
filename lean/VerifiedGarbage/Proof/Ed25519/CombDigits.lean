import VerifiedGarbage.Proof.Ed25519.CombConstants
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Module.NatInt

/-!
# The comb's digits and partial sums

Untrusted. The scalar `S < 2^256` has 64 nibbles `n_i`; the comb's digits are
`d_i = n_i - 8`, from `-8` to `7`. Step `c < 64` adds the digit `combIdx c`
(the odd digits `2c + 1` first, then the even digits `2(c - 32)`) times
`256^(c mod 32)`, and before the even digits the sum is multiplied by 16 and
`G = combGVal` added again. After step `c` the sum is `combVal S c`, and
`combVal S 64 = S` (`comb_sum`), since `G = 8 Σ_{j < 32} 256^j`.

A negative digit adds the negation of the table entry `|d|`: the cached
negation `negCached` swaps `Y - X` and `Y + X` and negates `2dT`.
-/

namespace VG.Proof.Ed25519

open VG.Impl.Ed25519 Edwards
open Spec.X25519 (Fe)

/-- Digit `i` of `S` in radix 16. -/
def nib (S i : Nat) : Nat := (S / 16 ^ i) % 16

/-- `Σ_{j < c} n_{2j+1} 256^j`. -/
def oddSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => oddSum S c + nib S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} n_{2j} 256^j`. -/
def evenSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => evenSum S c + nib S (2 * c) * 256 ^ c

theorem comb_partial (S : Nat) : ∀ n, 16 * oddSum S n + evenSum S n = S % 256 ^ n
  | 0 => by simp [oddSum, evenSum, Nat.mod_one]
  | n + 1 => by
    have ih := comb_partial S n
    have h16 : 256 ^ n = 16 ^ (2 * n) := by rw [pow_mul]; norm_num
    have hd : S / 16 ^ (2 * n + 1) = S / 16 ^ (2 * n) / 16 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hm : S % 256 ^ (n + 1) = S % 256 ^ n + 256 ^ n * (S / 256 ^ n % 256) := by
      rw [pow_succ, Nat.mod_mul]
    simp only [oddSum, evenSum, nib]
    rw [hm, ← ih, hd, h16]
    generalize S / 16 ^ (2 * n) = x
    generalize 16 ^ (2 * n) = y
    have : x % 256 = x % 16 + 16 * (x / 16 % 16) := by omega
    rw [this]; ring

/-- `Σ_{j < c} 256^j`. -/
def geom : Nat → Nat
  | 0 => 0
  | c + 1 => geom c + 256 ^ c

theorem combGVal_eq : combGVal = 8 * geom 32 := by decide

/-- The comb's digit `i`: `n_i - 8`, from `-8` to `7`. -/
def sdig (S i : Nat) : ℤ := (nib S i : ℤ) - 8

/-- `Σ_{j < c} d_{2j+1} 256^j`. -/
def oddSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => oddSumZ S c + sdig S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} d_{2j} 256^j`. -/
def evenSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => evenSumZ S c + sdig S (2 * c) * 256 ^ c

theorem oddSumZ_eq (S : Nat) : ∀ c, oddSumZ S c = oddSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [oddSumZ, oddSum, geom, oddSumZ_eq S c, sdig]
    push_cast; ring

theorem evenSumZ_eq (S : Nat) : ∀ c, evenSumZ S c = evenSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [evenSumZ, evenSum, geom, evenSumZ_eq S c, sdig]
    push_cast; ring

/-- The accumulator's multiple of `B` after `c` steps. -/
def combVal (S c : Nat) : ℤ :=
  if c ≤ 32 then combGVal + oddSumZ S c
  else 16 * (combGVal + oddSumZ S 32) + combGVal + evenSumZ S (c - 32)

theorem combVal_zero (S : Nat) : combVal S 0 = combGVal := by
  simp [combVal, oddSumZ]

theorem comb_sum {S : Nat} (hS : S < 2 ^ 256) : combVal S 64 = S := by
  simp only [combVal, show ¬ 64 ≤ 32 by decide, ↓reduceIte, show 64 - 32 = 32 from rfl, oddSumZ_eq,
    evenSumZ_eq, combGVal_eq]
  have h := comb_partial S 32
  rw [Nat.mod_eq_of_lt (by simpa using hS)] at h
  have h' : (16 * oddSum S 32 + evenSum S 32 : ℤ) = S := by exact_mod_cast h
  push_cast
  linear_combination h'

/-- The digit step `c` reads. -/
def combIdx (c : Nat) : Nat := if c < 32 then 2 * c + 1 else 2 * (c - 32)

theorem combIdx_lt {c : Nat} (hc : c < 64) : combIdx c < 64 := by
  unfold combIdx; split <;> omega

theorem combIdx_nib (S c : Nat) (hc : c < 64) :
    sdig S (combIdx c) * 256 ^ (c % 32) +
      (if c = 32 then 16 * combVal S c + combGVal else combVal S c) = combVal S (c + 1) := by
  unfold combIdx combVal
  by_cases h : c < 32
  · simp only [h, ↓reduceIte, show c ≠ 32 by omega, show c ≤ 32 by omega, show c + 1 ≤ 32 by omega,
      oddSumZ, Nat.mod_eq_of_lt h]
    ring
  · have hs : c + 1 - 32 = (c - 32) + 1 := by omega
    by_cases h32 : c = 32
    · subst h32
      simp only [show ¬ 32 < 32 by decide, ↓reduceIte, le_refl, show ¬ 33 ≤ 32 by decide,
        show 33 - 32 = 0 + 1 from rfl, evenSumZ]
      ring
    · simp only [h, h32, ↓reduceIte, show ¬ c ≤ 32 by omega, show ¬ c + 1 ≤ 32 by omega, hs, evenSumZ,
        show c % 32 = c - 32 by omega]
      ring

/-- A nibble from its four bits. -/
theorem nib_bits (S i : Nat) :
    nib S i = (((S / 2 ^ (4 * i + 3)) % 2 * 2 + (S / 2 ^ (4 * i + 2)) % 2) * 2 +
      (S / 2 ^ (4 * i + 1)) % 2) * 2 + (S / 2 ^ (4 * i)) % 2 := by
  have h16 : 16 ^ i = 2 ^ (4 * i) := by rw [pow_mul]; norm_num
  have e : ∀ t, S / 2 ^ (4 * i + t) = S / 16 ^ i / 2 ^ t := fun t => by
    rw [h16, Nat.div_div_eq_div_mul, ← pow_add]
  rw [nib, e 3, e 2, e 1, ← Nat.add_zero (4 * i), e 0]
  simp only [pow_zero, Nat.div_one, Nat.reducePow]
  omega

theorem nib_lt (S i : Nat) : nib S i < 16 := Nat.mod_lt _ (by decide)

/-- The magnitude of the digit `n - 8`. -/
def mag (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

theorem mag_lt {n : Nat} (hn : n < 16) : mag n < 9 := by unfold mag; split <;> omega

/-- The cached point `c` negated: `[Y + X, Y - X, -2dT, 2Z]` for `[Y - X, Y + X, 2dT, 2Z]`. -/
def negCached (c : Spec.Ed25519.Point) : Spec.Ed25519.Point := ⟨c.Y, c.X, 0 - c.Z, c.T⟩

theorem negCached_cache (q : Spec.Ed25519.Point) : negCached (cache q) = cache (negPoint q) := by
  simp only [negCached, cache, negPoint, Spec.Ed25519.Point.mk.injEq]
  refine ⟨toZ_inj.1 ?_, toZ_inj.1 ?_, toZ_inj.1 ?_, trivial⟩ <;>
    simp only [toZ_add, toZ_sub, toZ_mul, toZ_zero] <;> ring

/-- The entry for the digit `n - 8` of table `j`, negated for a negative digit, represents
`[(n - 8) 256^j]B`, with `Z = 1`. -/
theorem combEntry_ok (j n : Nat) (hj : j < 32) (hn : n < 16) :
    ∃ q, (if n < 8 then negCached (combCached j (mag n)) else combCached j (mag n)) = cache q ∧
      q.Z = 1 ∧ Rep q ((((n : ℤ) - 8) * 256 ^ j) • baseAff) := by
  obtain ⟨q₀, hq₀, hz, hr⟩ := combCached_ok j (mag n) hj (mag_lt hn)
  by_cases hlt : n < 8
  · refine ⟨negPoint q₀, by simp only [hlt, ↓reduceIte]; rw [hq₀, negCached_cache], hz, ?_⟩
    have e : ((n : ℤ) - 8) * 256 ^ j = -(((mag n * 256 ^ j : Nat) : ℤ)) := by
      simp only [mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : n ≤ 8)]; ring
    rw [e, neg_smul, natCast_zsmul]
    exact hr.neg
  · refine ⟨q₀, by simp only [hlt, ↓reduceIte]; exact hq₀, hz, ?_⟩
    have e : ((n : ℤ) - 8) * 256 ^ j = (((mag n * 256 ^ j : Nat) : ℤ)) := by
      simp only [mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : 8 ≤ n)]; ring
    rw [e, natCast_zsmul]
    exact hr

/-- `n` doublings represent `[2^n]`. -/
theorem powerPoint_rep {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep p a) :
    ∀ n, Rep (powerPoint p n) ((2 ^ n : Nat) • a)
  | 0 => by rw [pow_zero, one_smul]; exact h
  | n + 1 => by
    have := (powerPoint_rep h n).double
    rw [smul_smul] at this
    rw [powerPoint, pow_succ, Nat.mul_comm]
    exact this

theorem Rep.affine_x {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep p a) :
    p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2) = (a.x : Fe) := by
  show toZ (p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)) = a.x
  rw [toZ_mul, toZ_pow, h.x, mul_pow_inv h.z]

theorem Rep.affine_y {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep p a) :
    p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2) = (a.y : Fe) := by
  show toZ (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)) = a.y
  rw [toZ_mul, toZ_pow, h.y, mul_pow_inv h.z]

theorem zsmul_16 (v : ℤ) (g : Nat) (P : EPoint dZ) :
    (16 : Nat) • (v • P) + g • P = (16 * v + g) • P := by
  rw [add_smul, mul_smul, ← natCast_zsmul, ← natCast_zsmul]; rfl

end VG.Proof.Ed25519

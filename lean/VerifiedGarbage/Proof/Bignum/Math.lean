import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq
import VerifiedGarbage.Spec.Rsa
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Multiword arithmetic: the mathematics

Target-independent facts about the algorithms of the bignum code, on
naturals:

* `-m⁻¹ mod 2⁶⁴` by Newton's iteration (Hensel lifting): `x ↦ x (2 - a x)`
  doubles the number of low bits in which `a x ≡ 1`, and `a a ≡ 1 (mod 8)`
  for an odd `a` (`hensel_step`, `odd_sq`).
* A round of Montgomery multiplication by coarsely integrated operand
  scanning (CIOS): an accumulator `T < 2m` becomes `(T + a_i B + u m) / 2⁶⁴`,
  still below `2m` if `B < m` (`round_lt`), and congruent to
  `(T + a_i B) 2⁻⁶⁴` modulo `m` (`round_mul`).
* The conditional subtraction that ends it: below `2m`, subtracting `m`
  when it does not borrow is reduction modulo `m` (`csub_eq`).
-/

namespace VG.Proof.Bignum

/-! ## Newton's iteration for the inverse modulo `2⁶⁴` -/

/-- An odd square is `1` modulo 8. -/
theorem odd_sq (a : Nat) (ha : a % 2 = 1) : a * a % 8 = 1 := by
  have h : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  rw [Nat.mul_mod]
  rcases h with h | h | h | h <;> rw [h]

/-- One step of Newton's iteration, on integers: if `a x ≡ 1 (mod 2^j)` then
`a x (2 - a x) ≡ 1 (mod 2^(2j))`. -/
theorem hensel_step_int (a x : Int) (j : Nat) (h : (a * x - 1) % (2 ^ j : Int) = 0) :
    (a * (x * (2 - a * x)) - 1) % (2 ^ (2 * j) : Int) = 0 := by
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
  apply Int.emod_eq_zero_of_dvd
  refine ⟨-(k * k), ?_⟩
  have : a * (x * (2 - a * x)) - 1 = -((a * x - 1) * (a * x - 1)) := by ring
  rw [this, hk, two_mul, pow_add]
  ring

/-- A step of Newton's iteration computed modulo `2⁶⁴`: if `a x ≡ 1 (mod 2^j)`
and `x' ≡ x (2 - a x) (mod 2⁶⁴)` with `2 j ≤ 64`, then `a x' ≡ 1 (mod 2^(2j))`. -/
theorem newton_step {a x x' : Int} {j : Nat} (hj : 2 * j ≤ 64) (h : (a * x - 1) % (2 ^ j : Int) = 0)
    (hx : (x' - x * (2 - a * x)) % (2 ^ 64 : Int) = 0) : (a * x' - 1) % (2 ^ (2 * j) : Int) = 0 := by
  have h1 := Int.dvd_of_emod_eq_zero (hensel_step_int a x j h)
  have h2 : (2 ^ (2 * j) : Int) ∣ x' - x * (2 - a * x) :=
    (pow_dvd_pow 2 hj).trans (Int.dvd_of_emod_eq_zero hx)
  apply Int.emod_eq_zero_of_dvd
  have : a * x' - 1 = a * (x' - x * (2 - a * x)) + (a * (x * (2 - a * x)) - 1) := by ring
  rw [this]
  exact dvd_add (h2.mul_left a) h1

/-- Weakening a congruence modulo a power of two. -/
theorem emod_pow_weaken {y : Int} {i j : Nat} (hij : i ≤ j) (h : y % (2 ^ j : Int) = 0) :
    y % (2 ^ i : Int) = 0 :=
  Int.emod_eq_zero_of_dvd ((pow_dvd_pow 2 hij).trans (Int.dvd_of_emod_eq_zero h))

/-! ## A round of Montgomery multiplication -/

/-- The sum of a round: below `2⁶⁵ m`, if `T < 2m`, `a < 2⁶⁴`, `b < m` and
`u < 2⁶⁴`. -/
theorem round_sum_lt {T a b u m : Nat} (hT : T < 2 * m) (ha : a < 2 ^ 64) (hb : b < m)
    (hu : u < 2 ^ 64) : T + a * b + u * m < 2 ^ 65 * m := by
  have h1 : a * b ≤ (2 ^ 64 - 1) * b := Nat.mul_le_mul_right _ (by omega)
  have h2 : u * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul_right _ (by omega)
  have h3 : (2 ^ 64 - 1) * b ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.sub_mul, Nat.one_mul] at h1 h2 h3
  have : 2 ^ 65 * m = 2 * 2 ^ 64 * m := by norm_num
  omega

/-- A round keeps the accumulator below `2m`. -/
theorem round_lt {T T' a b u m : Nat} (h : 2 ^ 64 * T' = T + a * b + u * m) (hT : T < 2 * m)
    (ha : a < 2 ^ 64) (hb : b < m) (hu : u < 2 ^ 64) : T' < 2 * m := by
  have := round_sum_lt hT ha hb hu
  rw [← h, show 2 ^ 65 * m = 2 ^ 64 * (2 * m) by ring] at this
  exact Nat.lt_of_mul_lt_mul_left this

/-- The accumulator after a round, times `2⁶⁴`, modulo `m`. -/
theorem round_mod {T T' a b u m : Nat} (h : 2 ^ 64 * T' = T + a * b + u * m) :
    2 ^ 64 * T' % m = (T + a * b) % m := by
  rw [h, Nat.add_mul_mod_self_right]

/-- The rounds' invariant `2^(64 i) T ≡ A_i B (mod m)`, one round on. -/
theorem round_step {P T T' a b u m A : Nat} (h : 2 ^ 64 * T' = T + a * b + u * m)
    (hI : P * T % m = A * b % m) : P * 2 ^ 64 * T' % m = (A + P * a) * b % m := by
  have e : P * 2 ^ 64 * T' = P * T + P * a * b + P * u * m := by
    rw [Nat.mul_assoc, h]; ring
  rw [e, Nat.add_mul_mod_self_right, Nat.add_mod, hI, ← Nat.add_mod]
  congr 1
  ring

/-! ## The conditional subtraction -/

/-- Below `2m`, subtracting `m` when it does not borrow is reduction modulo `m`. -/
theorem csub_eq {T m : Nat} (h : T < 2 * m) : (if T < m then T else T - m) = T % m := by
  split
  · rw [Nat.mod_eq_of_lt (by assumption)]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- What `subMod` and `selectAcc` leave: for `T = T_l + R (T_w + 2⁶⁴ T_{w+1}) < 2m`
(`T_l < R` its low words, `m < R`) and `D + m = T_l + R c` (`D < R`, `c` the
borrow), `T_l` if `T_w < c` and `D` otherwise is `T mod m`. -/
theorem csub_result {Tl Tw Tw1 D m R c : Nat} (hm : m < R) (hD : D < R) (hc : c ≤ 1)
    (hTl : Tl < R) (hT : Tl + R * (Tw + 2 ^ 64 * Tw1) < 2 * m) (hsub : D + m = Tl + R * c) :
    (if Tw < c then Tl else D) = (Tl + R * (Tw + 2 ^ 64 * Tw1)) % m := by
  have hR : 0 < R := by omega
  -- The top words: `T_{w+1} = 0` and `T_w ≤ 1`.
  have h1 : Tw1 = 0 := by
    rcases Nat.eq_zero_or_pos Tw1 with h | h
    · exact h
    · have : R * 2 ^ 64 ≤ R * (Tw + 2 ^ 64 * Tw1) := Nat.mul_le_mul_left _ (by
        have := Nat.mul_le_mul_left (2 ^ 64) h; omega)
      have : R * 2 ^ 64 ≥ 2 * R := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by norm_num)
      omega
  subst h1
  simp only [Nat.mul_zero, Nat.add_zero] at hT ⊢
  rcases Nat.lt_or_ge Tw 1 with hw | hw
  · have hw0 : Tw = 0 := by omega
    subst hw0
    simp only [Nat.mul_zero, Nat.add_zero] at hT ⊢
    rcases Nat.lt_or_ge c 1 with hc0 | hc1
    · have : c = 0 := by omega
      subst this
      simp only [Nat.lt_irrefl, ite_false]
      simp only [Nat.mul_zero, Nat.add_zero] at hsub
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · have : c = 1 := by omega
      subst this
      simp only [Nat.zero_lt_one, ite_true]
      rw [Nat.mod_eq_of_lt (by omega)]
  · have : R * 1 ≤ R * Tw := Nat.mul_le_mul_left _ hw
    have hw1 : Tw = 1 := by
      rcases Nat.lt_or_ge Tw 2 with h | h
      · omega
      · have : R * 2 ≤ R * Tw := Nat.mul_le_mul_left _ h
        omega
    subst hw1
    have hc1 : c = 1 := by
      rcases Nat.lt_or_ge c 1 with h | h
      · have : c = 0 := by omega
        subst this; omega
      · omega
    subst hc1
    simp only [Nat.lt_irrefl, ite_false, Nat.mul_one] at hsub ⊢
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## Bytes and words -/

/-- Appending a byte keeps the low `r + 1` bytes. -/
theorem bytes_mod_step (X b r : Nat) (hb : b < 256) :
    (256 * X + b) % 256 ^ (r + 1) = 256 * (X % 256 ^ r) + b := by
  rw [Nat.pow_succ, Nat.mul_comm (256 ^ r) 256]
  have h1 : 256 * X + b = (256 * (X % 256 ^ r) + b) + 256 * 256 ^ r * (X / 256 ^ r) := by
    have := Nat.mod_add_div X (256 ^ r)
    calc 256 * X + b = 256 * (X % 256 ^ r + 256 ^ r * (X / 256 ^ r)) + b := by rw [this]
      _ = _ := by ring
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have := Nat.mod_lt X (show 0 < 256 ^ r by positivity)
  have : 256 * (X % 256 ^ r) + 256 ≤ 256 * 256 ^ r := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
  omega

/-- Appending a byte shifts the high bytes up by one. -/
theorem bytes_div_step (X b n : Nat) (hb : b < 256) : (256 * X + b) / 256 ^ (n + 1) = X / 256 ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, ← Nat.div_div_eq_div_mul,
    show (256 * X + b) / 256 = X by omega]

theorem pow256_8 : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num

/-! ## Montgomery form -/

/-- A power of two is invertible modulo an odd `m`. -/
theorem coprime_pow2 {m : Nat} (hm : m % 2 = 1) (k : Nat) : Nat.Coprime (2 ^ k) m :=
  Nat.Coprime.pow_left k (by show Nat.gcd 2 m = 1; rw [Nat.gcd_rec, hm]; rfl)

/-- Cancelling `R` from `o R ≡ c R (mod m)`, `R` invertible modulo `m`. -/
theorem mont_cancel {o c R m : Nat} (hR : Nat.Coprime R m) (h : o * R % m = c * R % m) : o % m = c % m :=
  Nat.ModEq.cancel_right_of_coprime hR.symm h

/-- `Spec.Rsa.powMod` is the power modulo `m`. -/
theorem powMod_eq (a e m : Nat) : Spec.Rsa.powMod a e m = a ^ e % m := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [Spec.Rsa.powMod]
    split
    · subst_vars; simp
    · rename_i he
      simp only
      rw [ih (e / 2) (by omega)]
      have : a ^ e = a ^ (e / 2) * a ^ (e / 2) * a ^ (e % 2) := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      split
      · rename_i h2
        rw [this, h2, Nat.pow_zero, Nat.mul_one]
        exact (Nat.mod_modEq _ m).mul (Nat.mod_modEq _ m)
      · rename_i h2
        rw [this, show e % 2 = 1 by omega, Nat.pow_one]
        exact ((Nat.mod_modEq _ m).trans ((Nat.mod_modEq _ m).mul (Nat.mod_modEq _ m))).mul_right a

/-! ## Exponentiation in Montgomery form -/

/-- A Montgomery squaring of `Y ≡ x^E R`: `x^(2E) R`. -/
theorem mont_sq {Y Y' x E R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = x ^ E * R % m)
    (h : Y' * R % m = Y * Y % m) : Y' % m = x ^ (2 * E) * R % m := by
  apply mont_cancel hR
  rw [h, Nat.mul_mod, hY, ← Nat.mul_mod]
  congr 1
  rw [show 2 * E = E + E by omega, Nat.pow_add]; ring

/-- A Montgomery multiplication of `Y ≡ x^E R` by `X ≡ x R`: `x^(E+1) R`. -/
theorem mont_mulx {Y Y' X x E R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = x ^ E * R % m)
    (hX : X % m = x * R % m) (h : Y' * R % m = Y * X % m) : Y' % m = x ^ (E + 1) * R % m := by
  apply mont_cancel hR
  rw [h, Nat.mul_mod, hY, hX, ← Nat.mul_mod]
  congr 1
  rw [Nat.pow_succ]; ring

end VG.Proof.Bignum

import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA: arithmetic modulo `q`, for every target

Untrusted: everything here is checked by Lean. Facts about `ℤ_q` (`Fin q`,
`q = 8380417`) as the natural numbers that represent its elements, and the
recipes that implementations reduce modulo `q` with, each proven for every
input in its range:

* addition and subtraction of reduced values, with one conditional
  subtraction of `q` (`val_add`, `val_sub`, `condSub`);
* `barrett`, a Barrett reduction of any `x < 2⁶⁴` with the high half of one
  64×64→128-bit product (`⌊x · ⌊2⁶⁴/q⌋ / 2⁶⁴⌋` is the quotient estimate),
  which leaves a value less than `2q` congruent to `x`, which `condSub` then
  reduces (`reduce_barrett`). A product of two reduced values is less than
  `q² < 2⁴⁶`, so it reduces any such product, or such a product plus a
  reduced value.

It also has the coefficients of polynomials (`getElem!_eq`, `ext_getElem!`)
and of their sums, differences and products (`add_get`, `sub_get`,
`mul_get`).
-/

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-! ## `ℤ_q` as natural numbers -/

theorem q_eq : q = 8380417 := rfl

theorem n_eq : n = 256 := rfl

/-- The element of `ℤ_q` that `x` represents, `x mod q`. -/
abbrev ofNat (x : Nat) : Zq := Fin.ofNat q x

theorem val_ofNat (x : Nat) : (ofNat x).val = x % q := rfl

theorem ofNat_val (a : Zq) : ofNat a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem ofNat_of_lt {x : Nat} (h : x < q) : (ofNat x).val = x := Nat.mod_eq_of_lt h

theorem val_add' (a b : Zq) : (a + b).val = (a.val + b.val) % q := Fin.val_add a b

theorem val_sub' (a b : Zq) : (a - b).val = (a.val + (q - b.val)) % q := by
  rw [Fin.val_sub, Nat.add_comm]

theorem val_mul (a b : Zq) : (a * b).val = a.val * b.val % q := Fin.val_mul a b

theorem val_neg (a : Zq) : (-a).val = (q - a.val) % q := Fin.val_neg' a

theorem val_pow (a : Zq) (k : Nat) : (a ^ k).val = a.val ^ k % q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (a ^ k * a).val = _
    rw [val_mul, ih, Nat.mod_mul_mod, Nat.pow_succ]

/-- The integer that represents an element of `ℤ_q` is less than 8380417. -/
theorem val_lt (a : Zq) : a.val < 8380417 := a.isLt

/-! ## Coefficients of polynomials -/

theorem getElem!_eq (f : Poly) {i : Nat} (hi : i < n) : f[i]! = f[i] := getElem!_pos f i hi

theorem getElem!_set!_self (f : Poly) {i : Nat} (hi : i < n) (x : Zq) : (f.set! i x)[i]! = x := by
  rw [getElem!_eq _ hi, Vector.getElem_set!, ite_eq_left rfl]

theorem getElem!_set!_ne (f : Poly) {i j : Nat} (hj : j < n) (h : i ≠ j) (x : Zq) :
    (f.set! i x)[j]! = f[j]! := by
  rw [getElem!_eq _ hj, getElem!_eq _ hj, Vector.getElem_set!, ite_eq_right h]

theorem ext_getElem! {f g : Poly} (h : ∀ i < n, f[i]! = g[i]!) : f = g :=
  Vector.ext fun i hi => by rw [← getElem!_eq f hi, ← getElem!_eq g hi]; exact h i hi

theorem add_get (f g : Poly) {i : Nat} (hi : i < n) : (add f g)[i]! = f[i]! + g[i]! := by
  rw [getElem!_eq _ hi, getElem!_eq _ hi, getElem!_eq _ hi]
  simp only [add, Vector.getElem_zipWith]

theorem sub_get (f g : Poly) {i : Nat} (hi : i < n) : (sub f g)[i]! = f[i]! - g[i]! := by
  rw [getElem!_eq _ hi, getElem!_eq _ hi, getElem!_eq _ hi]
  simp only [sub, Vector.getElem_zipWith]

theorem mul_get (f g : Poly) {i : Nat} (hi : i < n) : (multiplyNTT f g)[i]! = f[i]! * g[i]! := by
  rw [getElem!_eq _ hi, getElem!_eq _ hi, getElem!_eq _ hi]
  simp only [multiplyNTT, Vector.getElem_zipWith]

/-- A coefficient of `f` with each coefficient multiplied by `c`. -/
theorem map_mul_get (f : Poly) (c : Zq) {i : Nat} (hi : i < n) : (f.map (· * c))[i]! = f[i]! * c := by
  rw [getElem!_eq _ hi, getElem!_eq _ hi, Vector.getElem_map]

/-! ## Addition and subtraction of reduced values -/

/-- One conditional subtraction of `q`. -/
def condSub (t : Nat) : Nat := if q ≤ t then t - q else t

/-- One conditional subtraction reduces a value less than `2q`. -/
theorem condSub_eq {t : Nat} (h : t < 2 * q) : condSub t = t % q := by
  unfold condSub; rw [q_eq] at *; split <;> omega

theorem condSub_lt {t : Nat} (h : t < 2 * q) : condSub t < q := by
  unfold condSub; rw [q_eq] at *; split <;> omega

theorem val_add (a b : Zq) : (a + b).val = condSub (a.val + b.val) := by
  rw [val_add', condSub_eq (by have := a.isLt; have := b.isLt; omega)]

theorem val_sub (a b : Zq) : (a - b).val = condSub (a.val + q - b.val) := by
  have := a.isLt; have := b.isLt
  rw [val_sub', condSub_eq (by omega), show a.val + (q - b.val) = a.val + q - b.val by omega]

/-! ## Barrett reduction with the high half of a 128-bit product -/

/-- `⌊2⁶⁴ / q⌋`. -/
def barrettM : Nat := 2201172575745

theorem barrettM_eq : barrettM = 2 ^ 64 / q := by decide

/-- The quotient estimate of `barrett`: the high half of `x · ⌊2⁶⁴ / q⌋`. -/
def barrettQuot (x : Nat) : Nat := x * barrettM / 2 ^ 64

/-- `x - ⌊…⌋ · q`: `x` reduced to less than `2q` (`barrett_lt`). -/
def barrett (x : Nat) : Nat := x - barrettQuot x * q

/-- For `x < 2⁶⁴`: the estimate times `q` is at most `x`, and `x` is less
than the estimate plus 2, times `q`. -/
theorem barrett_bounds {x : Nat} (hx : x < 2 ^ 64) :
    barrettQuot x * q ≤ x ∧ x < barrettQuot x * q + 2 * q := by
  unfold barrettQuot barrettM
  rw [q_eq]
  constructor <;> omega

theorem barrett_lt {x : Nat} (hx : x < 2 ^ 64) : barrett x < 2 * q := by
  have := barrett_bounds hx
  unfold barrett
  omega

theorem barrett_mod {x : Nat} (hx : x < 2 ^ 64) : barrett x % q = x % q := by
  have h := (barrett_bounds hx).1
  unfold barrett
  generalize barrettQuot x = e at h
  have := Nat.mul_mod_left e q
  rw [q_eq] at *
  omega

/-- Reduction modulo `q` of `x < 2⁶⁴`. -/
theorem reduce_barrett {x : Nat} (hx : x < 2 ^ 64) : condSub (barrett x) = x % q := by
  rw [condSub_eq (barrett_lt hx), barrett_mod hx]

/-- A product of reduced values is less than `q² < 2⁴⁶`. -/
theorem mul_lt_q2 {a b : Nat} (ha : a < q) (hb : b < q) : a * b < 70231389093889 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt ha hb) (by decide)

end VG.Proof.MlDsa.Arith

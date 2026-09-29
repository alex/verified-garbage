import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM: arithmetic modulo `q`, for every target

Untrusted: everything here is checked by Lean. Facts about `ℤ_q` (`Fin q`)
as the natural numbers that represent its elements, and recipes that
implementations reduce modulo `q = 3329` with, each proven for every input
in its range:

* addition and subtraction of reduced values, with one conditional
  subtraction of `q` (`val_add`, `val_sub`, `condSub`);
* `barrett32`, a Barrett reduction whose products fit in 32 bits (for
  targets with only a 32-bit multiply, such as ARMv7), of any `x < 2²⁵`: a
  sum of two products of reduced values, such as `BaseCaseMultiply`
  computes, is less than `2q² < 2²⁵`;
* `barrett64`, a Barrett reduction with one 32×32→64-bit product, of any
  `x < 2³²`.

Each leaves a value less than `2q` congruent to `x`, which `condSub` then
reduces (`reduce32`, `reduce64`).

It also has the coefficients of polynomials (`getElem!_eq`, `ext_getElem!`)
and of their sums and differences (`add_get`, `sub_get`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## `ℤ_q` as natural numbers -/

theorem val_ofNat (x : Nat) : (ofNat x).val = x % q := rfl

theorem ofNat_val (a : Zq) : ofNat a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem ofNat_of_lt {x : Nat} (h : x < q) : (ofNat x).val = x := Nat.mod_eq_of_lt h

theorem ofNat_mod (x : Nat) : ofNat (x % q) = ofNat x := Fin.ext (Nat.mod_mod _ _)

theorem ofNat_eq_iff {x y : Nat} : ofNat x = ofNat y ↔ x % q = y % q :=
  ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

theorem val_add' (a b : Zq) : (a + b).val = (a.val + b.val) % q := Fin.val_add a b

theorem val_sub' (a b : Zq) : (a - b).val = (a.val + (q - b.val)) % q := by
  rw [Fin.val_sub, Nat.add_comm]

theorem val_mul (a b : Zq) : (a * b).val = a.val * b.val % q := Fin.val_mul a b

theorem val_pow (a : Zq) (k : Nat) : (a ^ k).val = a.val ^ k % q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (a ^ k * a).val = _
    rw [val_mul, ih, Nat.mod_mul_mod, Nat.pow_succ]

theorem ofNat_add (x y : Nat) : ofNat (x + y) = ofNat x + ofNat y :=
  Fin.ext (by rw [val_add', val_ofNat, val_ofNat, val_ofNat, Nat.add_mod])

theorem ofNat_mul (x y : Nat) : ofNat (x * y) = ofNat x * ofNat y :=
  Fin.ext (by rw [val_mul, val_ofNat, val_ofNat, val_ofNat, Nat.mul_mod])

theorem q_eq : q = 3329 := rfl

/-- The integer that represents an element of `ℤ_q` is less than 3329. -/
theorem val_lt (a : Zq) : a.val < 3329 := a.isLt

theorem val_zero : (0 : Zq).val = 0 := rfl

theorem zero_add' (a : Zq) : 0 + a = a := Fin.ext (by rw [val_add', val_zero, Nat.zero_add,
  Nat.mod_eq_of_lt a.isLt])

/-! ## Coefficients of polynomials -/

theorem n_eq : n = 256 := rfl

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

theorem zero_get {i : Nat} (hi : i < n) : zero[i]! = 0 := by
  rw [getElem!_eq _ hi]
  simp only [zero, Vector.getElem_replicate]

theorem zero_add_poly (f : Poly) : add zero f = f :=
  ext_getElem! fun i hi => by rw [add_get _ _ hi, zero_get hi, zero_add']

/-! ## Addition and subtraction of reduced values -/

/-- One conditional subtraction of `q`. -/
def condSub (t : Nat) : Nat := if q ≤ t then t - q else t

/-- One conditional subtraction reduces a value less than `2q`. -/
theorem condSub_eq {t : Nat} (h : t < 2 * q) : condSub t = t % q := by
  unfold condSub; rw [q_eq] at *; split <;> omega

theorem condSub_lt {t : Nat} (h : t < 2 * q) : condSub t < q := by
  unfold condSub; rw [q_eq] at *; split <;> omega

/-- `(a + b) mod q`, for reduced `a` and `b`: `a + b`, less `q` if that is
at least `q`. -/
theorem add_mod_q {a b : Nat} (ha : a < q) (hb : b < q) : (a + b) % q = condSub (a + b) :=
  (condSub_eq (by omega)).symm

/-- `(a - b) mod q`, for reduced `a` and `b`, as `a + q - b` reduced with one
conditional subtraction; that is `a - b` if `b ≤ a`, and `a + q - b`
otherwise. -/
theorem sub_mod_q {a b : Nat} (ha : a < q) (hb : b < q) :
    (a + q - b) % q = condSub (a + q - b) ∧
      condSub (a + q - b) = if b ≤ a then a - b else a + q - b := by
  refine ⟨(condSub_eq (by omega)).symm, ?_⟩
  unfold condSub; rw [q_eq] at *; split <;> split <;> omega

theorem val_add (a b : Zq) : (a + b).val = condSub (a.val + b.val) := by
  rw [val_add', condSub_eq (by have := a.isLt; have := b.isLt; omega)]

theorem val_sub (a b : Zq) : (a - b).val = condSub (a.val + q - b.val) := by
  have := a.isLt; have := b.isLt
  rw [val_sub', condSub_eq (by omega), show a.val + (q - b.val) = a.val + q - b.val by omega]

theorem val_sub_eq (a b : Zq) : (a - b).val = if b.val ≤ a.val then a.val - b.val else a.val + q - b.val := by
  rw [val_sub]; exact (sub_mod_q a.isLt b.isLt).2

/-! ## Barrett reduction with 32-bit products -/

/-- The quotient estimate of `barrett32`: `((x >> 11) · 161270) >> 18`,
where `161270 = ⌊2²⁹ / q⌋`. For `x < 2²⁵`, the product is less than `2³²`
(`barrett32_bounds`). -/
def barrett32Quot (x : Nat) : Nat := x / 2048 * 161270 / 262144

/-- `x - ⌊…⌋ · q`: `x` reduced to less than `2q` (`barrett32_lt`). -/
def barrett32 (x : Nat) : Nat := x - barrett32Quot x * q

/-- For `x < 2²⁵`: the product `(x >> 11) · 161270` fits in 32 bits, the
estimate times `q` is at most `x` (so the subtraction does not wrap), and
the estimate times `q` fits in 32 bits. -/
theorem barrett32_bounds {x : Nat} (hx : x < 2 ^ 25) :
    x / 2048 * 161270 < 2 ^ 32 ∧ barrett32Quot x * q ≤ x := by
  unfold barrett32Quot
  rw [q_eq]
  constructor <;> omega

theorem barrett32_lt {x : Nat} (hx : x < 2 ^ 25) : barrett32 x < 2 * q := by
  unfold barrett32 barrett32Quot
  rw [q_eq]
  omega

theorem barrett32_mod {x : Nat} (hx : x < 2 ^ 25) : barrett32 x % q = x % q := by
  have h := (barrett32_bounds hx).2
  unfold barrett32
  generalize barrett32Quot x = e at h
  have := Nat.mul_mod_left e q
  rw [q_eq] at *
  omega

/-- Reduction modulo `q` of `x < 2²⁵` with 32-bit arithmetic. -/
theorem reduce32 {x : Nat} (hx : x < 2 ^ 25) : condSub (barrett32 x) = x % q := by
  rw [condSub_eq (barrett32_lt hx), barrett32_mod hx]

/-! ## Barrett reduction with a 64-bit product -/

/-- The quotient estimate of `barrett64`: `(x · 1290167) >> 32`, where
`1290167 = ⌊2³² / q⌋`. -/
def barrett64Quot (x : Nat) : Nat := x * 1290167 / 4294967296

/-- `x - ⌊…⌋ · q`: `x` reduced to less than `2q` (`barrett64_lt`). -/
def barrett64 (x : Nat) : Nat := x - barrett64Quot x * q

/-- For `x < 2³²`: the product fits in 64 bits, and the estimate times `q`
is at most `x`. -/
theorem barrett64_bounds {x : Nat} (hx : x < 2 ^ 32) :
    x * 1290167 < 2 ^ 64 ∧ barrett64Quot x * q ≤ x := by
  unfold barrett64Quot
  rw [q_eq]
  constructor <;> omega

theorem barrett64_lt {x : Nat} (hx : x < 2 ^ 32) : barrett64 x < 2 * q := by
  unfold barrett64 barrett64Quot
  rw [q_eq]
  omega

theorem barrett64_mod {x : Nat} (hx : x < 2 ^ 32) : barrett64 x % q = x % q := by
  have h := (barrett64_bounds hx).2
  unfold barrett64
  generalize barrett64Quot x = e at h
  have := Nat.mul_mod_left e q
  rw [q_eq] at *
  omega

/-- Reduction modulo `q` of `x < 2³²` with one 64-bit product. -/
theorem reduce64 {x : Nat} (hx : x < 2 ^ 32) : condSub (barrett64 x) = x % q := by
  rw [condSub_eq (barrett64_lt hx), barrett64_mod hx]

/-! ## Products of reduced values -/

/-- A product of reduced values is less than `q² = 11082241`. -/
theorem mul_lt_q2 {a b : Nat} (ha : a < q) (hb : b < q) : a * b < 11082241 :=
  Nat.mul_lt_mul_of_lt_of_lt ha hb

/-- A product of reduced values, reduced with `barrett32`. -/
theorem val_mul_barrett32 (a b : Zq) : (a * b).val = condSub (barrett32 (a.val * b.val)) := by
  rw [val_mul, reduce32 (by have := mul_lt_q2 a.isLt b.isLt; omega)]

/-- `a₀b₀ + a₁b₁γ` of `BaseCaseMultiply`, with `a₁b₁` reduced first: the sum
is less than `2q² < 2²⁵`, so `barrett32` reduces it. -/
theorem val_mul_add_mul (a b c d : Zq) :
    (a * b + c * d).val = condSub (barrett32 (a.val * b.val + c.val * d.val)) := by
  have h1 := mul_lt_q2 a.isLt b.isLt
  have h2 := mul_lt_q2 c.isLt d.isLt
  rw [reduce32 (by omega), val_add', val_mul, val_mul, ← Nat.add_mod]

end VG.Proof.MlKem

import VerifiedGarbage.Proof.MlDsa.Arith.Zq

/-!
# ML-DSA: Montgomery reduction with 32-bit words, for every target

The reduction a target with 32-bit multiplications (a 32×32→64-bit product)
uses, for `R = 2³²`:

* `mont x = (x + m · q) / 2³²` for `m = (x mod 2³²) · (-q⁻¹ mod 2³²) mod 2³²`
  (`montQInv`): `x + m · q` is a multiple of `2³²` (`mont_mul`), so
  `mont x · 2³² ≡ x (mod q)`, and `mont x < 2q` if `x < q · 2³²`
  (`mont_lt`);
* as 32-bit halves (`mont_halves`): the high half of `x`, plus the high half
  of `m · q`, plus 1 exactly when the low half of `m · q` is not 0 (the
  carry of the sum of the low halves, which is `2³²` or `0`);
* what it computes modulo `q`: for a constant in Montgomery form
  `c · 2³² mod q`, `mont (a · (c · 2³² mod q)) ≡ a · c` (`mont_mulR`); and
  `mont (mont x · (2⁶⁴ mod q)) ≡ x` (`mont_mont_R2`), which multiplies two
  values without a constant in Montgomery form.
-/

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-- `-q⁻¹ mod 2³²`. -/
def montQInv : Nat := 4236238847

/-- The multiple of `q` that makes `x` divisible by `2³²`. -/
def montM (x : Nat) : Nat := x % 2 ^ 32 * montQInv % 2 ^ 32

/-- The Montgomery reduction of `x`: `(x + m · q) / 2³²`. -/
def mont (x : Nat) : Nat := (x + montM x * q) / 2 ^ 32

/-- The low half of `m · q` is `-x mod 2³²`. -/
theorem montM_mul_mod (x : Nat) : montM x * q % 2 ^ 32 = x % 2 ^ 32 * 4294967295 % 2 ^ 32 := by
  unfold montM
  rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, show montQInv * q % 2 ^ 32 = 4294967295 by decide,
    Nat.mod_mod]

theorem montM_lt (x : Nat) : montM x < 2 ^ 32 := Nat.mod_lt _ (by decide)

/-- `x + m · q` is a multiple of `2³²`. -/
theorem mont_mul (x : Nat) : mont x * 2 ^ 32 = x + montM x * q := by
  have h := montM_mul_mod x
  have hd : (x + montM x * q) % 2 ^ 32 = 0 :=
    (fun P (h : P % 2 ^ 32 = x % 2 ^ 32 * 4294967295 % 2 ^ 32) => show (x + P) % 2 ^ 32 = 0 by omega) _ h
  unfold mont
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)

theorem mont_lt {x : Nat} (hx : x < q * 2 ^ 32) : mont x < 2 * q := by
  have h := mont_mul x
  have hm : montM x * q < 2 ^ 32 * q := Nat.mul_lt_mul_of_pos_right (montM_lt x) (by decide)
  rw [q_eq] at hx hm ⊢
  exact (fun P (h : mont x * 2 ^ 32 = x + P) (hm : P < 2 ^ 32 * 8380417) => show mont x < 2 * 8380417 by omega)
    _ h hm

/-- `mont x` from the halves of `x` and of `m · q`, as a 32-bit machine computes it. -/
theorem mont_halves (x : Nat) :
    mont x = x / 2 ^ 32 + montM x * q / 2 ^ 32 + (if 1 ≤ montM x * q % 2 ^ 32 then 1 else 0) := by
  have h := montM_mul_mod x
  unfold mont
  exact (fun P (h : P % 2 ^ 32 = x % 2 ^ 32 * 4294967295 % 2 ^ 32) =>
    show (x + P) / 2 ^ 32 = x / 2 ^ 32 + P / 2 ^ 32 + (if 1 ≤ P % 2 ^ 32 then 1 else 0) by split <;> omega) _ h

/-- `mont x · 2³² ≡ x (mod q)`. -/
theorem mont_mod (x : Nat) : mont x * 2 ^ 32 % q = x % q := by
  rw [mont_mul, Nat.add_mul_mod_self_right]

/-- Cancelling the factor `2³²` modulo `q`: `2³² · 8265825 ≡ 1`. -/
theorem cancel_R {u v : Nat} (h : u * 2 ^ 32 % q = v * 2 ^ 32 % q) : u % q = v % q := by
  have e : ∀ w : Nat, w % q = w * 2 ^ 32 % q * 8265825 % q := fun w => by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, show 2 ^ 32 * 8265825 % q = 1 by decide, Nat.mul_one,
      Nat.mod_mod]
  rw [e u, e v, h]

/-- With a constant `c` in Montgomery form: `mont (a · (c · 2³² mod q)) ≡ a · c`. -/
theorem mont_mulR (a c : Nat) : mont (a * (c * 2 ^ 32 % q)) % q = a * c % q := by
  refine cancel_R ?_
  rw [mont_mod, Nat.mul_mod_mod, Nat.mul_assoc]

/-- Two reductions, the second of a product with `2⁶⁴ mod q`: `x` modulo `q`. -/
theorem mont_mont_R2 (x : Nat) : mont (mont x * (2 ^ 64 % q)) % q = x % q := by
  refine cancel_R ?_
  rw [mont_mod, Nat.mul_mod_mod, show 2 ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, ← Nat.mul_assoc, Nat.mul_mod,
    mont_mod, ← Nat.mul_mod]

/-- `mont` of a value less than `q · 2³²`, reduced by one conditional subtraction. -/
theorem condSub_mont {x : Nat} (hx : x < q * 2 ^ 32) : condSub (mont x) = mont x % q :=
  condSub_eq (mont_lt hx)

end VG.Proof.MlDsa.Arith

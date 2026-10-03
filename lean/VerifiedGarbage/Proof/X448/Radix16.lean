import VerifiedGarbage.Proof.X448.Field
import Batteries.Tactic.Init
import Batteries.Logic

/-!
# X448: radix-2¹⁶ arithmetic

The twenty-eight limbs of a field element, carries, and reduction using `2^448 =
2^224 + 1` modulo p. These lemmas do not depend on an instruction set.
-/

namespace VG.Proof.X448.Radix16

open VG.Spec.X448

def radix : Nat := 2 ^ 16
def full : Nat := radix ^ 28
def half : Nat := radix ^ 14

theorem full_eq : full = P + (half + 1) := by decide +kernel
theorem half_sq : half * half = full := by decide +kernel

/-- Read `n` limbs, lowest first. -/
def valN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => valN f n + radix ^ n * f n

theorem valN_succ (f : Nat → Nat) (n : Nat) :
    valN f (n + 1) = valN f n + radix ^ n * f n := rfl

theorem valN_congr {f g : Nat → Nat} {n : Nat}
    (h : ∀ i < n, f i = g i) : valN f n = valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [valN, valN, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem valN_add (f g : Nat → Nat) (n : Nat) :
    valN (fun i => f i + g i) n = valN f n + valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [valN, valN, valN, ih, Nat.mul_add]; omega

theorem valN_scale (c : Nat) (f : Nat → Nat) (n : Nat) :
    valN (fun i => c * f i) n = c * valN f n := by
  induction n with
  | zero => simp only [valN, Nat.mul_zero]
  | succ n ih => rw [valN, valN, ih, Nat.mul_add, Nat.mul_left_comm (radix ^ n) c]

theorem valN_split (f : Nat → Nat) (a b : Nat) :
    valN f (a + b) = valN f a + radix ^ a * valN (fun i => f (a + i)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, valN, Nat.mul_zero]
  | succ b ih => rw [Nat.add_succ, valN, valN, ih, Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem valN_lt {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < radix) :
    valN f n < radix ^ n := by
  induction n with
  | zero => simp only [valN, Nat.pow_zero]; decide
  | succ n ih =>
    have hn := h n (by omega)
    have hp := ih fun i hi => h i (by omega)
    have hm := Nat.mul_le_mul_left (radix ^ n) hn
    rw [Nat.mul_succ] at hm
    rw [valN, Nat.pow_succ]
    omega

theorem valN_zero (n : Nat) : valN (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [valN, ih, Nat.mul_zero, Nat.add_zero]

/-- Changing one limb changes the value at that limb's weight. -/
theorem valN_update {f g : Nat → Nat} {n k v : Nat} (hk : k < n)
    (h : ∀ i < n, g i = if i = k then f i + v else f i) :
    valN g n = valN f n + radix ^ k * v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn : k = n
    · subst k
      have he : valN g n = valN f n := valN_congr fun i hi => by
        rw [h i (by omega), ite_eq_right (by omega)]
      rw [valN, valN, he, h n (by omega), ite_eq_left rfl, Nat.mul_add]
      omega
    · rw [valN, valN, ih (by omega) (fun i hi => h i (by omega)),
        h n (by omega), ite_eq_right (Ne.symm hn)]
      omega

/-- The incoming carry at position `n`. -/
def carry (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (f n + carry f n) / radix

def digit (f : Nat → Nat) (i : Nat) : Nat := (f i + carry f i) % radix

theorem digit_lt (f : Nat → Nat) (i : Nat) : digit f i < radix :=
  Nat.mod_lt _ (by decide)

theorem pass_eq (f : Nat → Nat) (n : Nat) :
    valN (digit f) n + radix ^ n * carry f n = valN f n := by
  induction n with
  | zero => simp only [valN, carry, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have hd := Nat.mod_add_div (f n + carry f n) radix
    change digit f n + radix * carry f (n + 1) = f n + carry f n at hd
    rw [valN, valN, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, hd,
      Nat.mul_add]
    omega

theorem carry_bound {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i ≤ 2 ^ 32 - radix) :
    carry f n < 2 ^ 16 := by
  induction n with
  | zero => simp only [carry]; decide
  | succ n ih =>
    have hi := ih fun i hi => h i (by omega)
    have hn := h n (by omega)
    simp only [radix] at hn hi ⊢
    simp only [carry, radix]
    omega

/-- The carry-out folded into the normalized limbs at positions 0 and 14. -/
def folded (f : Nat → Nat) (i : Nat) : Nat :=
  digit f i + if i = 0 ∨ i = 14 then carry f 28 else 0

theorem folded_val (f : Nat → Nat) :
    valN (folded f) 28 = valN (digit f) 28 + (half + 1) * carry f 28 := by
  change valN (fun i => digit f i + if i = 0 ∨ i = 14 then carry f 28 else 0) 28 = _
  rw [valN_add]
  congr 1
  simp only [valN, half]
  simp (config := {decide := true}) only [ite_true, ite_false, Nat.mul_zero, Nat.add_zero,
    Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  grind

theorem fold_mod (lo hi : Nat) :
    (lo + full * hi) % P = (lo + (half + 1) * hi) % P := by
  rw [full_eq, Nat.add_mul, Nat.add_left_comm lo, Nat.add_comm (P * hi), Nat.add_mul_mod_self_left]

theorem folded_mod (f : Nat → Nat) : valN (folded f) 28 % P = valN f 28 % P := by
  rw [folded_val, ← fold_mod, ← pass_eq f 28]
  rfl

theorem folded_bound {f : Nat → Nat} (h : ∀ i < 28, f i ≤ 2 ^ 32 - radix) :
    ∀ i < 28, folded f i ≤ 2 ^ 32 - radix := by
  have hc := carry_bound h
  intro i _
  have hd := digit_lt f i
  simp only [folded]
  split <;> simp only [radix] at hd ⊢ <;> omega

/-- After two folds, no carry remains beyond the 448-bit field width. -/
theorem final_carry {f : Nat → Nat} (h : ∀ i < 28, f i ≤ 2 ^ 32 - radix) :
    carry (folded (folded f)) 28 = 0 := by
  by_contra hn
  have hn : 1 ≤ carry (folded (folded f)) 28 := Nat.pos_of_ne_zero hn
  have c0 := carry_bound h
  have v0 := valN_lt (n := 28) (fun i _ => digit_lt f i)
  have v1 := valN_lt (n := 28) (fun i _ => digit_lt (folded f) i)
  have e1 := pass_eq (folded f) 28
  have e2 := pass_eq (folded (folded f)) 28
  rw [folded_val] at e1 e2
  change valN (digit f) 28 < full at v0
  change valN (digit (folded f)) 28 < full at v1
  change valN (digit (folded f)) 28 + full * carry (folded f) 28 = _ at e1
  change valN (digit (folded (folded f))) 28 + full * carry (folded (folded f)) 28 = _ at e2
  have small : (half + 1) * (2 ^ 16 + 1) < full := by decide +kernel
  have c1 : carry (folded f) 28 ≤ 1 := by
    by_contra hc
    have hb := Nat.mul_le_mul_left (half + 1) (Nat.le_of_lt c0)
    have hp := Nat.mul_le_mul_left full (show 2 ≤ carry (folded f) 28 from by omega)
    omega
  rcases Nat.eq_zero_or_pos (carry (folded f) 28) with hc | hc
  · rw [hc, Nat.mul_zero, Nat.add_zero] at e2
    have hp := Nat.mul_le_mul_left full hn
    omega
  · have hc : carry (folded f) 28 = 1 := by omega
    rw [hc, Nat.mul_one] at e1 e2
    have hb := Nat.mul_le_mul_left (half + 1) (Nat.le_of_lt c0)
    have hp := Nat.mul_le_mul_left full hn
    omega

def normalized (f : Nat → Nat) : Nat → Nat := digit (folded (folded f))

theorem normalized_mod {f : Nat → Nat} (h : ∀ i < 28, f i ≤ 2 ^ 32 - radix) :
    valN (normalized f) 28 % P = valN f 28 % P := by
  have e := pass_eq (folded (folded f)) 28
  rw [final_carry h, Nat.mul_zero, Nat.add_zero] at e
  rw [normalized, e, folded_mod, folded_mod]


def bias (i : Nat) : Nat := if i = 14 then 2 * radix - 4 else 2 * radix - 2

theorem bias_val : valN bias 28 = 2 * P := by decide +kernel

theorem bias_bound (i : Nat) : radix ≤ bias i ∧ bias i < 2 * radix := by
  unfold bias
  split <;> decide

def difference (f g : Nat → Nat) (i : Nat) : Nat := f i + bias i - g i

theorem difference_bound {f g : Nat → Nat} (hf : ∀ i < 28, f i < radix) :
    ∀ i < 28, difference f g i < 2 ^ 32 - radix := by
  intro i hi
  have h1 := hf i hi
  have h2 := (bias_bound i).2
  have hr : 3 * radix < 2 ^ 32 - radix := by decide
  simp only [difference]
  omega

theorem difference_val {f g : Nat → Nat} (hg : ∀ i < 28, g i < radix) :
    valN (difference f g) 28 + valN g 28 = valN f 28 + 2 * P := by
  rw [← valN_add]
  have he : valN (fun i => difference f g i + g i) 28 = valN (fun i => f i + bias i) 28 := by
    apply valN_congr
    intro i hi
    have h1 := hg i hi
    have h2 := (bias_bound i).1
    simp only [difference]
    omega
  rw [he, valN_add, bias_val]


def freezeCoeff (f : Nat → Nat) (i : Nat) : Nat := f i + if i = 0 ∨ i = 14 then 1 else 0

theorem freezeCoeff_val (f : Nat → Nat) : valN (freezeCoeff f) 28 = valN f 28 + (half + 1) := by
  change valN (fun i => f i + if i = 0 ∨ i = 14 then 1 else 0) 28 = _
  rw [valN_add]
  congr 1

theorem freezeCoeff_bound {f : Nat → Nat} (hf : ∀ i < 28, f i < radix) :
    ∀ i < 28, freezeCoeff f i < 2 ^ 32 - radix := by
  intro i hi
  have h := hf i hi
  have hr : radix + 1 < 2 ^ 32 - radix := by decide
  simp only [freezeCoeff]
  split <;> omega

theorem freeze_carry {f : Nat → Nat} (hf : ∀ i < 28, f i < radix) :
    carry (freezeCoeff f) 28 = if P ≤ valN f 28 then 1 else 0 := by
  have hv := valN_lt hf
  have hd := valN_lt (n := 28) (fun i _ => digit_lt (freezeCoeff f) i)
  have e := pass_eq (freezeCoeff f) 28
  rw [freezeCoeff_val] at e
  change valN f 28 < full at hv
  change valN (digit (freezeCoeff f)) 28 < full at hd
  change valN (digit (freezeCoeff f)) 28 + full * carry (freezeCoeff f) 28 = _ at e
  have hp : half + 1 < P := by decide +kernel
  have he := full_eq
  have hq : carry (freezeCoeff f) 28 ≤ 1 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left full (show 2 ≤ carry (freezeCoeff f) 28 by omega)
    omega
  rcases Nat.eq_zero_or_pos (carry (freezeCoeff f) 28) with h | h
  · rw [h, Nat.mul_zero, Nat.add_zero] at e
    rw [ite_eq_right (by omega), h]
  · have h : carry (freezeCoeff f) 28 = 1 := by omega
    rw [h, Nat.mul_one] at e
    rw [ite_eq_left (by omega), h]

theorem freeze_value {f : Nat → Nat} (hf : ∀ i < 28, f i < radix) :
    (if carry (freezeCoeff f) 28 = 1 then valN (digit (freezeCoeff f)) 28 else valN f 28) =
      valN f 28 % P := by
  have hv := valN_lt hf
  change valN f 28 < full at hv
  have e := pass_eq (freezeCoeff f) 28
  rw [freezeCoeff_val, freeze_carry hf] at e
  rw [freeze_carry hf]
  have hp : half + 1 < P := by decide +kernel
  have he := full_eq
  by_cases h : P ≤ valN f 28
  · rw [ite_eq_left h, ite_eq_left rfl]
    rw [ite_eq_left h, Nat.mul_one] at e
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : valN f 28 - P < P)]
    change valN (digit (freezeCoeff f)) 28 + full = _ at e
    omega
  · rw [ite_eq_right h, ite_eq_right (by decide), Nat.mod_eq_of_lt (by omega)]




/-- Row `i` of a product, before carrying. -/
def rowC (acc a b : Nat → Nat) (i j : Nat) : Nat := a i * b j + acc (i + j)

/-- The limbs after row `i`, including its carry. -/
def rowAcc (acc a b : Nat → Nat) (i k : Nat) : Nat :=
  if k < i then acc k else if k < i + 28 then digit (rowC acc a b i) (k - i)
  else carry (rowC acc a b i) 28

theorem row_val {acc a b : Nat → Nat} {i : Nat}
    (hv : valN acc (i + 28) = valN a i * valN b 28) :
    valN (rowAcc acc a b i) (i + 29) = valN a (i + 1) * valN b 28 := by
  have e1 : valN (rowAcc acc a b i) i = valN acc i :=
    valN_congr fun k hk => by simp only [rowAcc, hk, ite_true]
  have e2 : valN (fun k => rowAcc acc a b i (i + k)) 29 =
      valN (digit (rowC acc a b i)) 28 + radix ^ 28 * carry (rowC acc a b i) 28 := by
    rw [valN_succ, valN_congr (g := digit (rowC acc a b i)) fun k hk => by
      simp only [rowAcc, show ¬ i + k < i by omega, show i + k < i + 28 by omega,
        ite_false, ite_true, Nat.add_sub_cancel_left]]
    simp only [rowAcc, show ¬ i + 28 < i by omega, Nat.lt_irrefl, ite_false]
  have e3 : valN (rowC acc a b i) 28 = a i * valN b 28 + valN (fun k => acc (i + k)) 28 := by
    rw [← valN_scale, ← valN_add]; rfl
  rw [valN_split _ i 29, e1, e2, pass_eq, e3, valN_succ a i, Nat.add_mul, ← hv,
    valN_split acc i 28, Nat.mul_add, Nat.mul_assoc]
  omega

theorem rowC_bound {acc a b : Nat → Nat} {i j : Nat} (ha : a i < radix) (hb : b j < radix)
    (hacc : acc (i + j) < radix) : rowC acc a b i j ≤ 2 ^ 32 - radix := by
  simp only [radix] at ha hb hacc ⊢
  have : a i * b j ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
  simp only [rowC]
  omega

theorem rowAcc_lt {acc a b : Nat → Nat} {i : Nat} (hacc : ∀ k < i, acc k < radix)
    (hc : ∀ j < 28, rowC acc a b i j ≤ 2 ^ 32 - radix) :
    ∀ k < i + 29, rowAcc acc a b i k < radix := by
  intro k _
  simp only [rowAcc]
  split
  · exact hacc k (by omega)
  · split
    · exact digit_lt _ _
    · exact carry_bound hc

/-- Coefficients of degree 28–23 fold once; 42–31 fold twice. -/
def reduced (f : Nat → Nat) (k : Nat) : Nat :=
  f k + f (k + 28) + if k < 14 then f (k + 42) else f (k + 14) + f (k + 28)

theorem reduced_val (f : Nat → Nat) :
    valN (reduced f) 28 =
      (valN f 14 + valN (fun i => f (28 + i)) 14 + valN (fun i => f (42 + i)) 14) +
      half * (valN (fun i => f (14 + i)) 14 + valN (fun i => f (42 + i)) 14 +
        valN (fun i => f (28 + i)) 14 + valN (fun i => f (42 + i)) 14) := by
  rw [show 28 = 14 + 14 from rfl, valN_split]
  apply congrArg₂ (· + ·)
  · rw [← valN_add, ← valN_add]
    apply valN_congr
    intro i hi
    simp only [reduced, ite_eq_left hi, Nat.add_comm i]
  · apply congrArg (radix ^ 14 * ·)
    rw [← valN_add, ← valN_add, ← valN_add]
    apply valN_congr
    intro i _
    simp only [reduced, ite_eq_right (by omega : ¬ 14 + i < 14)]
    rw [show 14 + i + 28 = 42 + i by omega, show 14 + i + 14 = 28 + i by omega]
    simp only [Nat.reduceAdd]
    omega

theorem reduced_mod (f : Nat → Nat) : valN (reduced f) 28 % P = valN f 56 % P := by
  have hp : P = full - half - 1 := by decide +kernel
  have he : valN f 56 = valN (reduced f) 28 +
      P * (valN (fun i => f (28 + i)) 14 + (half + 1) * valN (fun i => f (42 + i)) 14) := by
    rw [reduced_val, show 56 = 28 + 28 from rfl, valN_split,
      show 28 = 14 + 14 from rfl, valN_split, valN_split]
    simp only [← Nat.add_assoc, Nat.reduceAdd]
    simp only [hp, full, half, radix, Nat.reducePow]
    omega
  rw [he, Nat.add_mul_mod_self_left]

theorem reduced_bound {f : Nat → Nat} (h : ∀ i < 56, f i < radix) :
    ∀ i < 28, reduced f i ≤ 2 ^ 32 - radix := by
  intro i hi
  have h0 := h i (by omega)
  have h1 := h (i + 28) (by omega)
  simp only [radix] at h0 h1 ⊢
  simp only [reduced]
  split
  · have h2 := h (i + 42) (by omega); simp only [radix] at h2; omega
  · have h2 := h (i + 14) (by omega); simp only [radix] at h2; omega


end VG.Proof.X448.Radix16

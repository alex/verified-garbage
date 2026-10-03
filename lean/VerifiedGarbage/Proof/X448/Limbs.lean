import VerifiedGarbage.Proof.X448.Field
import Batteries.Tactic.Init

/-!
# X448: radix-2²⁸ arithmetic

The sixteen limbs of a field element, carries, and reduction using `2^448 =
2^224 + 1` modulo p. These lemmas do not depend on an instruction set.
-/

namespace VG.Proof.X448

open VG.Spec.X448

def radix : Nat := 2 ^ 28
def full : Nat := radix ^ 16
def half : Nat := radix ^ 8

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

theorem carry_bound {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < 2 ^ 62) :
    carry f n < 2 ^ 35 := by
  induction n with
  | zero => simp only [carry]; decide
  | succ n ih =>
    have hi := ih fun i hi => h i (by omega)
    have hn := h n (by omega)
    simp only [carry, radix]
    omega

/-- The carry-out folded into the normalized limbs at positions 0 and 8. -/
def folded (f : Nat → Nat) (i : Nat) : Nat :=
  digit f i + if i = 0 ∨ i = 8 then carry f 16 else 0

theorem folded_val (f : Nat → Nat) :
    valN (folded f) 16 = valN (digit f) 16 + (half + 1) * carry f 16 := by
  change valN (fun i => digit f i + if i = 0 ∨ i = 8 then carry f 16 else 0) 16 = _
  rw [valN_add]
  congr 1
  simp only [valN, half]
  simp (config := {decide := true}) only [ite_true, ite_false, Nat.mul_zero, Nat.add_zero,
    Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  grind

theorem fold_mod (lo hi : Nat) :
    (lo + full * hi) % P = (lo + (half + 1) * hi) % P := by
  rw [full_eq, Nat.add_mul, Nat.add_left_comm lo, Nat.add_comm (P * hi), Nat.add_mul_mod_self_left]

theorem folded_mod (f : Nat → Nat) : valN (folded f) 16 % P = valN f 16 % P := by
  rw [folded_val, ← fold_mod, ← pass_eq f 16]
  rfl

theorem folded_bound {f : Nat → Nat} (h : ∀ i < 16, f i < 2 ^ 62) :
    ∀ i < 16, folded f i < 2 ^ 62 := by
  have hc := carry_bound h
  intro i _
  have hd := digit_lt f i
  simp only [folded]
  split <;> simp only [radix] at hd <;> omega

/-- After two folds, no carry remains beyond the 448-bit field width. -/
theorem final_carry {f : Nat → Nat} (h : ∀ i < 16, f i < 2 ^ 62) :
    carry (folded (folded f)) 16 = 0 := by
  by_contra hn
  have hn : 1 ≤ carry (folded (folded f)) 16 := Nat.pos_of_ne_zero hn
  have c0 := carry_bound h
  have v0 := valN_lt (n := 16) (fun i _ => digit_lt f i)
  have v1 := valN_lt (n := 16) (fun i _ => digit_lt (folded f) i)
  have e1 := pass_eq (folded f) 16
  have e2 := pass_eq (folded (folded f)) 16
  rw [folded_val] at e1 e2
  change valN (digit f) 16 < full at v0
  change valN (digit (folded f)) 16 < full at v1
  change valN (digit (folded f)) 16 + full * carry (folded f) 16 = _ at e1
  change valN (digit (folded (folded f))) 16 + full * carry (folded (folded f)) 16 = _ at e2
  have small : (half + 1) * (2 ^ 35 + 1) < full := by decide +kernel
  have c1 : carry (folded f) 16 ≤ 1 := by
    by_contra hc
    have hb := Nat.mul_le_mul_left (half + 1) (Nat.le_of_lt c0)
    have hp := Nat.mul_le_mul_left full (show 2 ≤ carry (folded f) 16 from by omega)
    omega
  rcases Nat.eq_zero_or_pos (carry (folded f) 16) with hc | hc
  · rw [hc, Nat.mul_zero, Nat.add_zero] at e2
    have hp := Nat.mul_le_mul_left full hn
    omega
  · have hc : carry (folded f) 16 = 1 := by omega
    rw [hc, Nat.mul_one] at e1 e2
    have hb := Nat.mul_le_mul_left (half + 1) (Nat.le_of_lt c0)
    have hp := Nat.mul_le_mul_left full hn
    omega

def normalized (f : Nat → Nat) : Nat → Nat := digit (folded (folded f))

theorem normalized_mod {f : Nat → Nat} (h : ∀ i < 16, f i < 2 ^ 62) :
    valN (normalized f) 16 % P = valN f 16 % P := by
  have e := pass_eq (folded (folded f)) 16
  rw [final_carry h, Nat.mul_zero, Nat.add_zero] at e
  rw [normalized, e, folded_mod, folded_mod]

end VG.Proof.X448

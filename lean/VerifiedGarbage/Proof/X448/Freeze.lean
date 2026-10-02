import VerifiedGarbage.Proof.X448.Limbs

/-!
# X448: canonical reduction

For a normalized value below 2⁴⁴⁸, adding 1 + 2²²⁴ produces a carry exactly
when it is at least p. Selecting the carried result in that case gives the
canonical residue.
-/

namespace VG.Proof.X448

open VG.Spec.X448

def freezeCoeff (f : Nat → Nat) (i : Nat) : Nat := f i + if i = 0 ∨ i = 8 then 1 else 0

theorem freezeCoeff_val (f : Nat → Nat) : valN (freezeCoeff f) 16 = valN f 16 + (half + 1) := by
  change valN (fun i => f i + if i = 0 ∨ i = 8 then 1 else 0) 16 = _
  rw [valN_add]
  congr 1

theorem freezeCoeff_bound {f : Nat → Nat} (hf : ∀ i < 16, f i < radix) :
    ∀ i < 16, freezeCoeff f i < 2 ^ 62 := by
  intro i hi
  have h := hf i hi
  have hr : radix + 1 < 2 ^ 62 := by decide
  simp only [freezeCoeff]
  split <;> omega

theorem freeze_carry {f : Nat → Nat} (hf : ∀ i < 16, f i < radix) :
    carry (freezeCoeff f) 16 = if P ≤ valN f 16 then 1 else 0 := by
  have hv := valN_lt hf
  have hd := valN_lt (n := 16) (fun i _ => digit_lt (freezeCoeff f) i)
  have e := pass_eq (freezeCoeff f) 16
  rw [freezeCoeff_val] at e
  change valN f 16 < full at hv
  change valN (digit (freezeCoeff f)) 16 < full at hd
  change valN (digit (freezeCoeff f)) 16 + full * carry (freezeCoeff f) 16 = _ at e
  have hp : half + 1 < P := by decide +kernel
  have he := full_eq
  have hq : carry (freezeCoeff f) 16 ≤ 1 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left full (show 2 ≤ carry (freezeCoeff f) 16 by omega)
    omega
  rcases Nat.eq_zero_or_pos (carry (freezeCoeff f) 16) with h | h
  · rw [h, Nat.mul_zero, Nat.add_zero] at e
    rw [ite_eq_right (by omega), h]
  · have h : carry (freezeCoeff f) 16 = 1 := by omega
    rw [h, Nat.mul_one] at e
    rw [ite_eq_left (by omega), h]

theorem freeze_value {f : Nat → Nat} (hf : ∀ i < 16, f i < radix) :
    (if carry (freezeCoeff f) 16 = 1 then valN (digit (freezeCoeff f)) 16 else valN f 16) =
      valN f 16 % P := by
  have hv := valN_lt hf
  change valN f 16 < full at hv
  have e := pass_eq (freezeCoeff f) 16
  rw [freezeCoeff_val, freeze_carry hf] at e
  rw [freeze_carry hf]
  have hp : half + 1 < P := by decide +kernel
  have he := full_eq
  by_cases h : P ≤ valN f 16
  · rw [ite_eq_left h, ite_eq_left rfl]
    rw [ite_eq_left h, Nat.mul_one] at e
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : valN f 16 - P < P)]
    change valN (digit (freezeCoeff f)) 16 + full = _ at e
    omega
  · rw [ite_eq_right h, ite_eq_right (by decide), Nat.mod_eq_of_lt (by omega)]

end VG.Proof.X448

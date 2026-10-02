import VerifiedGarbage.Proof.X448.Wide.Limbs

/-! Untrusted: tighter carry bounds for coefficients after the first fold. -/
namespace VG.Proof.X448.Wide

theorem carry_small {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < 2 ^ 63 + radix) :
    carry f n < 2 ^ 8 := by
  induction n with
  | zero => simp only [carry]; decide
  | succ n ih =>
    have hi := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    simp only [carry, radix]
    simp only [radix] at hn
    omega

theorem folded_small {f : Nat → Nat} (h : ∀ i < 8, f i < 2 ^ 118) :
    ∀ i < 8, folded f i < 2 ^ 63 + radix := by
  have hc := carry_bound h
  intro i _
  have hd := digit_lt f i
  simp only [folded]
  split <;> omega

end VG.Proof.X448.Wide

import VerifiedGarbage.Proof.MlDsa.Round.Mem

/-!
# ML-DSA: counting the 1s of a hint from its first coefficient, for every target

`onesTo h i`, the number of 1s among coefficients `0` to `i - 1` of a hint
polynomial, for a loop that counts them in order (`onesTo_succ`), and all 256
of them are those of `hintOnes` (`hintOnes_onesTo`).
-/

namespace VG.Proof.MlDsa.Round

open VG.Spec.MlDsa

/-- The number of 1s among coefficients `0` to `i - 1` of a hint polynomial. -/
def onesTo (h : Vector Bool n) (i : Nat) : Nat := ((List.range i).filter fun j => h[j]!).length

theorem onesTo_zero (h : Vector Bool n) : onesTo h 0 = 0 := rfl

theorem onesTo_succ (h : Vector Bool n) (i : Nat) : onesTo h (i + 1) = onesTo h i + h[i]!.toNat := by
  unfold onesTo
  rw [List.range_succ, List.filter_append, List.length_append]
  cases hb : h[i]! <;> simp [List.filter, hb]

theorem hintOnes_onesTo (h : Vector Bool n) : hintOnes [h] = onesTo h n := by
  rw [hintOnes_single, onesFrom, onesTo, Nat.sub_zero, List.range_eq_range']

end VG.Proof.MlDsa.Round

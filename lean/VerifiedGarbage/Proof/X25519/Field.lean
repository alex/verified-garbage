import VerifiedGarbage.Spec.X25519

/-!
# X25519: field elements as natural numbers

Untrusted: everything here is checked by Lean. Implementations compute with
natural numbers (the limbs of a field element, as any number standing for
its residue modulo `p`); `toFe` reads one as an element of `GF(p)`, and the
lemmas here turn what an implementation proves about its numbers (modulo
`p`) into the operations of `Spec/X25519.lean`, in the order the spec writes
them.
-/

namespace VG.Proof.X25519

open VG.Spec.X25519

/-- A natural number as an element of `GF(p)`: its residue. -/
def toFe (x : Nat) : Fe := Fin.ofNat P x

theorem toFe_val (x : Nat) : (toFe x).val = x % P := rfl

theorem toFe_eq_iff {a b : Nat} : toFe a = toFe b ↔ a % P = b % P := Fin.ext_iff

theorem toFe_congr {a b : Nat} (h : a % P = b % P) : toFe a = toFe b := toFe_eq_iff.2 h

theorem toFe_self (x : Fe) : toFe x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

theorem toFe_mod (x : Nat) : toFe (x % P) = toFe x := toFe_congr (Nat.mod_mod _ _)

theorem toFe_mul {a b c : Nat} (h : c % P = a * b % P) : toFe c = toFe a * toFe b := by
  apply Fin.ext
  show c % P = (a % P) * (b % P) % P
  rw [h, Nat.mul_mod]

theorem toFe_add {a b c : Nat} (h : c % P = (a + b) % P) : toFe c = toFe a + toFe b := by
  apply Fin.ext
  show c % P = (a % P + b % P) % P
  rw [h, Nat.add_mod]

/-- A difference: `c + b ≡ a`. -/
theorem toFe_sub {a b c : Nat} (h : (c + b) % P = a % P) : toFe c = toFe a - toFe b := by
  apply Fin.ext
  show c % P = ((P - b % P) + a % P) % P
  have hx : c % P < P := Nat.mod_lt _ (by decide)
  have hy : b % P < P := Nat.mod_lt _ (by decide)
  rw [← h, Nat.add_mod c b]
  generalize c % P = x at *
  generalize b % P = y at *
  rcases Nat.lt_or_ge (x + y) P with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, show P - y + (x + y) = x + P by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hx]
  · rw [show (x + y) % P = x + y - P by rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)],
      show P - y + (x + y - P) = x by omega, Nat.mod_eq_of_lt hx]

/-- A multiplication by `a24`, written as the spec writes it. -/
theorem toFe_a24 {a c : Nat} (h : c % P = 121665 * a % P) : toFe c = a24 * toFe a := by
  apply Fin.ext
  show c % P = (121665 % P) * (a % P) % P
  rw [h, Nat.mul_mod]

theorem toFe_zero : toFe 0 = 0 := rfl
theorem toFe_one : toFe 1 = 1 := rfl

/-- `2²⁵⁶ ≡ 38` modulo `p`: the top of a 512-bit product folds into its
bottom times 38. -/
theorem fold256 (lo hi : Nat) : (lo + 2 ^ 256 * hi) % P = (lo + 38 * hi) % P := by
  rw [show lo + 2 ^ 256 * hi = lo + 38 * hi + P * (2 * hi) by simp only [P]; omega,
    Nat.add_mul_mod_self_left]

/-- `2²⁵⁵ ≡ 19` modulo `p`. -/
theorem fold255 (lo hi : Nat) : (lo + 2 ^ 255 * hi) % P = (lo + 19 * hi) % P := by
  rw [show lo + 2 ^ 255 * hi = lo + 19 * hi + P * hi by simp only [P]; omega,
    Nat.add_mul_mod_self_left]

end VG.Proof.X25519

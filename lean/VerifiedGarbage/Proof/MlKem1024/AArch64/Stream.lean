import VerifiedGarbage.Proof.MlKem.AArch64.Width
import VerifiedGarbage.Proof.MlKem.Compress1024
import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress

/-!
# ML-KEM-1024 on AArch64: bits streaming through a register

Untrusted: everything here is checked by Lean. The arithmetic of the
compression loops of ML-KEM-1024, which stream the bits of a group of
8 coefficients of `d` bits (`8d` bits, `d` bytes) through `x9`, for
`d` = 5 and 11:

* a number's low bits determine its low digits (`digits_range_mod`), so
  byte `j` of a group is byte `j` of the number of its first coefficients
  once they hold its bits (`byte_of_mod`);
* adding a digit above the bits a register holds (`add_shift_div`), and
  shifting a byte out of it (`div_div8`).
-/

namespace VG.Proof.MlKem1024.AArch64

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64

/-- The widths of ML-KEM-1024's compression. -/
theorem mem_widths {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) : d = 5 ∨ d = 11 :=
  mem_compressWidths1024 hd

/-- The digits of the first `e'` values, modulo `2^(w e)` for `e ≤ e'`, are
those of the first `e`. -/
theorem digits_range_mod {w : Nat} {f : Nat → Nat} (hf : ∀ i, f i < 2 ^ w) {e : Nat} :
    ∀ {e'}, e ≤ e' → digits w ((List.range e').map f) % 2 ^ (w * e) = digits w ((List.range e).map f)
  | e', h => by
    induction e' with
    | zero =>
      have : e = 0 := by omega
      subst this
      exact Nat.mod_eq_of_lt (digits_range_lt hf 0)
    | succ e' ih =>
      rcases (by omega : e ≤ e' ∨ e = e' + 1) with h' | rfl
      · rw [digits_range_succ, show w * e' = w * e + w * (e' - e) by
          rw [← Nat.mul_add, Nat.add_sub_cancel' h'], Nat.pow_add, Nat.mul_assoc,
          Nat.add_mul_mod_self_left, ih h']
      · exact Nat.mod_eq_of_lt (digits_range_lt hf _)

/-- Bits `[s, s + w)` of numbers equal modulo `2^M`, for `s + w ≤ M`. -/
theorem bits_of_mod {a b M s w : Nat} (h : a % 2 ^ M = b % 2 ^ M) (hs : s + w ≤ M) :
    a / 2 ^ s % 2 ^ w = b / 2 ^ s % 2 ^ w := by
  have e : ∀ x, x / 2 ^ s % 2 ^ w = x % 2 ^ M % 2 ^ (s + w) / 2 ^ s := fun x => by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hs), Nat.pow_add, Nat.mod_mul_right_div_self]
  rw [e, e b, h]

/-- Byte `j` of numbers equal modulo `2^M`, for `8 j + 8 ≤ M`. -/
theorem byte_of_mod {a b M j : Nat} (h : a % 2 ^ M = b % 2 ^ M) (hj : 8 * j + 8 ≤ M) :
    a / 2 ^ (8 * j) % 256 = b / 2 ^ (8 * j) % 256 :=
  bits_of_mod (w := 8) h hj

/-- A digit `c` added above the `D mod 8` bits left of a number `a < 2^D`
after its `⌊D / 8⌋` whole bytes. -/
theorem add_shift_div (a c D : Nat) :
    a / 2 ^ (8 * (D / 8)) + c * 2 ^ (D % 8) = (a + 2 ^ D * c) / 2 ^ (8 * (D / 8)) := by
  have e : 2 ^ D * c = 2 ^ (8 * (D / 8)) * (c * 2 ^ (D % 8)) := by
    conv => lhs; rw [← Nat.div_add_mod D 8]
    rw [Nat.pow_add, Nat.mul_comm c, Nat.mul_assoc]
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

/-- The bits left of a number `a < 2^D` after its `⌊D / 8⌋` whole bytes. -/
theorem shift_lt {a D : Nat} (h : a < 2 ^ D) : a / 2 ^ (8 * (D / 8)) < 2 ^ (D % 8) := by
  refine Nat.div_lt_of_lt_mul ?_
  rw [← Nat.pow_add, Nat.div_add_mod]
  exact h

/-- A byte `b` added at bit `8 j` of a number `a`, above the `D ≤ 8 j` bits
shifted out. -/
theorem add_byte_div {a b D j : Nat} (h : D ≤ 8 * j) :
    a / 2 ^ D + b * 2 ^ (8 * j - D) = (a + 2 ^ (8 * j) * b) / 2 ^ D := by
  have e : 2 ^ (8 * j) * b = 2 ^ D * (b * 2 ^ (8 * j - D)) := by
    rw [Nat.mul_comm b, ← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' h]
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

/-- A number less than `2^N`, shifted right by `D ≤ N`. -/
theorem div_lt_sub {a D N : Nat} (h : a < 2 ^ N) (hD : D ≤ N) : a / 2 ^ D < 2 ^ (N - D) := by
  refine Nat.div_lt_of_lt_mul ?_
  rw [← Nat.pow_add, Nat.add_sub_cancel' hD]
  exact h

/-- A byte shifted out. -/
theorem div_div8 (a j : Nat) : a / 2 ^ (8 * j) / 2 ^ 8 = a / 2 ^ (8 * (j + 1)) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]

end VG.Proof.MlKem1024.AArch64

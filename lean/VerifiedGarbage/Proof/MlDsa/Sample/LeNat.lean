import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask

/-!
# ML-DSA: the fields of a group of bytes, for every target

The `c`-bit fields of a byte string `L` (`leNat L / 2^(ic) mod 2^c`) as an
implementation reads them a group at a time: from byte `o` on, the string is
`leNat (L.drop o)` (`leNat_drop`); the fields in its first 8 bytes are those
of the `u64` of them (`field_low`); and a field that straddles the 8th byte is
the top bits of the `u64` plus the next bytes above them
(`leNat_take_succ`, `split_div`).
-/

namespace VG.Proof.MlDsa.Sample

theorem leNat_lt : ∀ L : List Byte, leNat L < 2 ^ (8 * L.length)
  | [] => by simp [leNat]
  | c :: L => by
    have := leNat_lt L
    have := c.isLt
    rw [leNat, List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (8 * L.length))]
    have : c.toNat + 2 ^ 8 * leNat L ≤ 2 ^ 8 - 1 + 2 ^ 8 * (2 ^ (8 * L.length) - 1) := by
      have := Nat.mul_le_mul_left (2 ^ 8) (Nat.le_sub_one_of_lt (leNat_lt L))
      omega
    have h1 : 1 ≤ 2 ^ (8 * L.length) := Nat.one_le_two_pow
    rw [Nat.mul_sub_one] at this
    omega

/-- The string from byte `k` on. -/
theorem leNat_drop : ∀ (L : List Byte) (k : Nat), leNat L / 2 ^ (8 * k) = leNat (L.drop k)
  | L, 0 => by simp
  | [], k + 1 => by simp [leNat]
  | c :: L, k + 1 => by
    rw [List.drop_succ_cons, ← leNat_drop L k, leNat, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (8 * k)),
      ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt c.isLt, Nat.zero_add]

/-- A field in the first 8 bytes. -/
theorem field_low (D : List Byte) {P c : Nat} (h : P + c ≤ 64) :
    leNat (D.take 8) / 2 ^ P % 2 ^ c = leNat D / 2 ^ P % 2 ^ c := leNat_take_bits D (by omega)

/-- The first `k + 1` bytes: the first `k`, and byte `k` above them. -/
theorem leNat_take_succ (D : List Byte) {k : Nat} (hk : k < D.length) :
    leNat (D.take (k + 1)) = leNat (D.take k) + 2 ^ (8 * k) * (D.getD k 0).toNat := by
  induction D generalizing k with
  | nil => simp at hk
  | cons c D ih =>
    cases k with
    | zero => simp [leNat]
    | succ k =>
      rw [List.take_succ_cons, List.take_succ_cons, leNat, leNat, ih (by simp at hk; omega), List.getD_cons_succ,
        Nat.mul_succ, Nat.pow_add, Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm (2 ^ 8), Nat.mul_assoc,
        Nat.mul_comm (2 ^ 8) (D.getD k 0).toNat]

/-- Dividing a number of two parts by a power of two below the split. -/
theorem split_div (A B : Nat) {P M : Nat} (hP : P ≤ M) : (A + 2 ^ M * B) / 2 ^ P = A / 2 ^ P + 2 ^ (M - P) * B := by
  rw [show 2 ^ M = 2 ^ P * 2 ^ (M - P) by rw [← Nat.pow_add]; congr 1; omega, Nat.mul_assoc,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos P)]

end VG.Proof.MlDsa.Sample

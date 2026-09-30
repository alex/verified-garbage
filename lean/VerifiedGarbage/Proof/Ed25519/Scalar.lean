import VerifiedGarbage.Spec.Ed25519

/-!
# Ed25519 scalar arithmetic: binary reduction

Untrusted. A remainder below L becomes a value below 2L after consuming
one bit, so one conditional subtraction is sufficient.
-/

namespace VG.Proof.Ed25519

open VG.Spec.Ed25519

theorem order_pos : 0 < L := by decide
theorem order_bound : 2 * L < 2 ^ 256 := by decide

theorem reduce_bit {r b : Nat} (hr : r < L) (hb : b < 2) :
    (2 * r + b) % L = if 2 * r + b < L then 2 * r + b else 2 * r + b - L := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem decodeLE_cons (b : Byte) (bs : List Byte) :
    decodeLE (b :: bs) = b.toNat + 256 * decodeLE bs := rfl

theorem reduce_cons (b : Byte) (bs : List Byte) :
    decodeLE (b :: bs) % L = (256 * (decodeLE bs % L) + b.toNat) % L := by
  rw [decodeLE_cons, Nat.add_comm]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- Consume n bits from high to low, reducing after every bit. -/
def consumeBits (b : BitVec 64) (n r : Nat) : Nat :=
  (List.range n).reverse.foldl (fun v j => (2 * v + (b.getLsbD j).toNat) % L) r

theorem consumeBits_succ (b : BitVec 64) (n r : Nat) :
    consumeBits b (n + 1) r = consumeBits b n ((2 * r + (b.getLsbD n).toNat) % L) := by
  simp only [consumeBits, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem consumeBits_eq (b : BitVec 64) (n r : Nat) (hr : r < L) :
    consumeBits b n r = (2 ^ n * r + b.toNat % 2 ^ n) % L := by
  induction n generalizing r with
  | zero => simp only [consumeBits, List.range_zero, List.reverse_nil, List.foldl_nil,
      Nat.pow_zero, Nat.one_mul, Nat.mod_one, Nat.add_zero, Nat.mod_eq_of_lt hr]
  | succ n ih =>
    rw [consumeBits_succ, ih _ (Nat.mod_lt _ order_pos)]
    have hmod (a x z : Nat) : (a * (x % L) + z) % L = (a * x + z) % L := by
      rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
    rw [hmod, Nat.pow_succ, Nat.mod_mul]
    simp only [← BitVec.testBit_toNat, Nat.toNat_testBit, Nat.mul_add, Nat.mul_assoc]
    congr 1
    omega

end VG.Proof.Ed25519

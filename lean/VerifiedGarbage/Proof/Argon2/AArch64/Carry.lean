import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # Arithmetic facts for ARM64's subtraction carry -/
namespace VG.Proof.Argon2.AArch64

theorem sub_value (a b : BitVec 64) : a + ~~~b + 1#64 = a - b := by
  change a + ~~~b + 1#64 = a - b
  rw [BitVec.add_assoc, ← BitVec.neg_eq_not_add, ← BitVec.sub_eq_add_neg]

theorem sub_carry (a b : BitVec 64) :
    decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + 1) = decide (b.toNat ≤ a.toNat) := by
  rw [BitVec.toNat_not]
  have hb := b.isLt
  have h : (2 ^ 64 ≤ a.toNat + (2 ^ 64 - 1 - b.toNat) + 1) ↔ b.toNat ≤ a.toNat := by
    simp only [Nat.reducePow] at *
    omega
  simp only [h]

theorem borrow_mask (x : BitVec 64) (b : Bool) :
    x + ~~~x + BitVec.ofNat 64 b.toNat = if b then 0 else -1 := by
  rw [BitVec.not_eq_neg_add, BitVec.sub_eq_add_neg, ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg x x, BitVec.sub_self]
  cases b <;> rfl
end VG.Proof.Argon2.AArch64

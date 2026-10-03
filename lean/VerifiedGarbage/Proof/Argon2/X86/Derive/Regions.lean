import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.TCB.X86.Target

/-!
# Regions at 32-bit addresses

The derivation's regions all lie at 32-bit addresses (`x.setWidth 64`), so
whether they are disjoint, contain an access or lie in one another is a
question about the addresses' values: `disj32`, `contains32` and `sub32`
reduce each to arithmetic on `toNat`, for `omega`.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG

theorem toNat_w (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem disj32 {x y : BitVec 32} {n m : Nat} (h : x.toNat + n ≤ y.toNat ∨ y.toNat + m ≤ x.toNat)
    (hn : x.toNat + n ≤ 2 ^ 32) (hm : y.toNat + m ≤ 2 ^ 32) :
    Region.Disjoint ⟨x.setWidth 64, n⟩ ⟨y.setWidth 64, m⟩ := by
  rcases h with h | h
  · exact Offset.disjoint_of_le (by simp only [toNat_w]; omega) (by simp only [toNat_w]; omega)
  · exact (Offset.disjoint_of_le (r₁ := ⟨y.setWidth 64, m⟩) (by simp only [toNat_w]; omega)
      (by simp only [toNat_w]; omega)).symm

theorem contains32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Contains ⟨y.setWidth 64, m⟩ (x.setWidth 64) n := by
  simp only [Region.Contains]
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, toNat_w]; exact h₁), toNat_w, toNat_w]
  omega

theorem sub32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Sub ⟨x.setWidth 64, n⟩ ⟨y.setWidth 64, m⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  have hx := toNat_w x
  have hy := toNat_w y
  have := x.isLt
  bv_omega

/-- `x - k`, as a number. -/
theorem sub_nat {x : BitVec 32} {k : Nat} (h : k ≤ x.toNat) :
    (x - BitVec.ofNat 32 k).toNat = x.toNat - k := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
  rw [show 2 ^ 32 - k + x.toNat = (x.toNat - k) + 2 ^ 32 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- `x + k`, as a number. -/
theorem add_nat {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt h]

end VG.Proof.Argon2.X86.Derive

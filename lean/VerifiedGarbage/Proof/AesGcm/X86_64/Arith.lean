import VerifiedGarbage.Proof.AesGcm.X86_64.Env

/-!
# AES-GCM on x86-64: arithmetic on lengths

Untrusted: everything here is checked by Lean. The 64-bit operations on
lengths and offsets the code does, as operations on natural numbers.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

theorem imm_eq {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem setWidth_imm {n : Nat} : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 (n % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem shr4 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem shr2 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 2 = BitVec.ofNat 64 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem and15 (x : BitVec 64) : x &&& (BitVec.ofNat 32 15).signExtend 64 = BitVec.ofNat 64 (x.toNat % 16) := by
  rw [imm_eq (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 15) (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- `ZF` after `x - y` (or a test of `x` with itself), as natural numbers. -/
theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) :=
  Offset.ofNat_sub_ofNat_beq ha hb

theorem and_self_beq {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a &&& BitVec.ofNat 64 a == 0) = decide (a = 0) := by
  rw [BitVec.and_self]
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat_of_lt ha] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

/-- `16 n`, by four doublings. -/
theorem times16_val (n : Nat) :
    BitVec.ofNat 64 n + BitVec.ofNat 64 n + (BitVec.ofNat 64 n + BitVec.ofNat 64 n) +
        (BitVec.ofNat 64 n + BitVec.ofNat 64 n + (BitVec.ofNat 64 n + BitVec.ofNat 64 n)) +
      (BitVec.ofNat 64 n + BitVec.ofNat 64 n + (BitVec.ofNat 64 n + BitVec.ofNat 64 n) +
        (BitVec.ofNat 64 n + BitVec.ofNat 64 n + (BitVec.ofNat 64 n + BitVec.ofNat 64 n))) =
      BitVec.ofNat 64 (16 * n) := by
  simp only [ofNat_add_ofNat]; congr 1; omega

/-- `8 n`, by three doublings. -/
theorem times8_val (x : BitVec 64) :
    x + x + (x + x) + (x + x + (x + x)) = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end VG.Proof.AesGcm.X86_64

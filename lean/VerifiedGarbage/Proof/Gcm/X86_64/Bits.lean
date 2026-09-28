import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Gcm.Spec

/-!
# GHASH on x86-64: the bit manipulations of one step, and loading blocks

Untrusted: everything here is checked by Lean. What the instructions of a
step (`Impl.Gcm.X86_64.step`) compute on the two halves of a 128-bit value,
stated on the whole value; and big-endian blocks as two `bswap`ped loads.
-/

namespace VG.Proof.Gcm.X86_64

open VG.Proof.Gcm

open VG.Impl.Gcm.X86_64 (rHigh)

/-- `sbb r, r`. -/
theorem sbb_self (r : BitVec 64) (c : Bool) :
    r - r - (BitVec.ofBool c).setWidth 64 = if c then BitVec.allOnes 64 else 0#64 := by
  cases c <;> simp

/-- `add lo, lo; adc hi, hi` shifts `hi ++ lo` left by one bit. -/
theorem shl1 (a b : BitVec 64) :
    (a + a + (BitVec.ofBool (decide (2 ^ 64 ≤ b.toNat + b.toNat))).setWidth 64) ++ (b + b) =
      (a ++ b) <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_append, BitVec.toNat_shiftLeft, toNat_append, BitVec.toNat_add,
    BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool, Nat.shiftLeft_eq]
  by_cases h : 2 ^ 64 ≤ b.toNat + b.toNat
  · rw [decide_eq_true h]; simp only [Bool.toNat_true]; omega
  · rw [decide_eq_false h]; simp only [Bool.toNat_false]; omega

/-- … and leaves the most significant bit in CF. -/
theorem shl1_cf (a b : BitVec 64) :
    decide (2 ^ 64 ≤ a.toNat + a.toNat + (decide (2 ^ 64 ≤ b.toNat + b.toNat)).toNat) =
      (a ++ b).msb := by
  rw [BitVec.msb_append]
  show _ = a.msb
  rw [BitVec.msb_eq_decide]
  by_cases h : 2 ^ 64 ≤ b.toNat + b.toNat
  · rw [decide_eq_true h]; simp only [Bool.toNat_true]; apply decide_eq_decide.mpr; omega
  · rw [decide_eq_false h]; simp only [Bool.toNat_false]; apply decide_eq_decide.mpr; omega

theorem mask_z (zh zl vh vl : BitVec 64) (c : Bool) :
    (zh ^^^ (vh &&& if c then BitVec.allOnes 64 else 0#64)) ++
      (zl ^^^ (vl &&& if c then BitVec.allOnes 64 else 0#64)) =
      if c then (zh ++ zl) ^^^ (vh ++ vl) else zh ++ zl := by
  cases c
  · simp only [Bool.false_eq_true, ite_false, BitVec.and_zero, BitVec.xor_zero]
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_append]

theorem R_eq : Spec.Gcm.R = rHigh ++ 0#64 := by decide

theorem shr1 (vh vl : BitVec 64) :
    (vh ++ vl) >>> 1 = (vh >>> 1) ++ ((vl >>> 1) ||| (vh &&& BitVec.signExtend 64 (1 : BitVec 32)).rotateRight 1) := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_and]
  rcases (by omega : i < 63 ∨ i = 63 ∨ 64 ≤ i) with h | rfl | h
  · simp [h, show 1 + i < 64 by omega, show i < 64 by omega]
  · simp
  · simp only [show ¬ 1 + i < 64 by omega, show ¬ i < 64 by omega, ite_false]
    congr 1; omega

theorem update_v (vh vl m : BitVec 64) :
    ((vh >>> 1) ^^^ ((m - m - (BitVec.ofBool (vl.getLsbD (1 - 1))).setWidth 64) &&& rHigh)) ++
      ((vl >>> 1) ||| (vh &&& BitVec.signExtend 64 (1 : BitVec 32)).rotateRight 1) =
      if (vh ++ vl).getLsbD 0 then ((vh ++ vl) >>> 1) ^^^ Spec.Gcm.R else (vh ++ vl) >>> 1 := by
  rw [sbb_self, shr1, R_eq, BitVec.getLsbD_append]
  simp only [show (0 : Nat) < 64 by decide, ite_true, Nat.sub_self]
  cases vl.getLsbD 0
  · simp only [Bool.false_eq_true, ite_false, BitVec.zero_and, BitVec.xor_zero]
  · simp only [ite_true, BitVec.allOnes_and]
    rw [BitVec.xor_append, BitVec.xor_zero]

/-- The 16 bytes as 8 bytes. -/
theorem bytesAt_16 (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 16 =
    [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2),
      m (p + BitVec.ofNat 64 3), m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5),
      m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7), m (p + BitVec.ofNat 64 8),
      m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
      m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
      m (p + BitVec.ofNat 64 15)] := rfl

/-- Two 8-byte loads and `bswap`s read a block. -/
theorem blockAt_bswap (m : Mem) (p : Addr) :
    X86_64.bswap64 (m.readW (p + BitVec.ofNat 64 0) 64) ++
      X86_64.bswap64 (m.readW (p + BitVec.ofNat 64 8) 64) = Spec.Gcm.blockAt m p := by
  have e : ∀ j : Nat, j < 15 → p + BitVec.ofNat 64 j + 1 = p + BitVec.ofNat 64 (j + 1) :=
    fun j hj => by bv_omega
  rw [X86_64.bswap64_readW, X86_64.bswap64_readW, e 0 (by omega), e 1 (by omega), e 2 (by omega),
    e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 8 (by omega), e 9 (by omega),
    e 10 (by omega), e 11 (by omega), e 12 (by omega), e 13 (by omega), e 14 (by omega),
    Spec.Gcm.blockAt, bytesAt_16, ofBytes_16]

theorem getLsbD_bswap64 (a : BitVec 64) (i : Nat) (hi : i < 64) :
    (X86_64.bswap64 a).getLsbD i = a.getLsbD (8 * (7 - i / 8) + i % 8) := by
  simp only [X86_64.bswap64]
  rw [X86_64.getLsbD_cat8]
  simp only [BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
    (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ 56 ≤ i) with
    h | h | h | h | h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right] <;>
  (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

theorem bswap64_bswap64 (a : BitVec 64) : X86_64.bswap64 (X86_64.bswap64 a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_bswap64 _ _ hi, getLsbD_bswap64 _ _ (by omega)]
  congr 1; omega

end VG.Proof.Gcm.X86_64

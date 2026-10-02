import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.TCB.Arm.Isa

/-!
# AES-GCM on ARMv7: words and the lengths block

Untrusted: everything here is checked by Lean. `rev` is `byteRev32`; the
bytes of a block of two 64-bit values are their big-endian bytes
(`toBytes_append64`); and `8 x` of a 64-bit `x = hi:lo`, as the code computes
it with shifts (`shl3_words`).
-/

namespace VG.Proof.AesGcm.Arm

open VG
open VG.Spec.Gcm (be64 toBytes)

theorem rev_eq : VG.Arm.rev = byteRev32 := rfl

theorem toBytes_append64 (a c : BitVec 64) : toBytes (a ++ c) = be64 a.toNat ++ be64 c.toNat := by
  have ha := a.isLt; have hc := c.isLt
  have e : (a ++ c).toNat = a.toNat * 2 ^ 64 + c.toNat := Proof.Gcm.toNat_append a c
  simp only [toBytes, be64, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, e]
    omega

/-- `8 x`, of `x = hi:lo`, in two words, as `lsl #3` and `orr` with `lsr #29`. -/
theorem shl3_words (hi lo : BitVec 32) :
    (((hi <<< 3) ||| (lo >>> 29)) ++ (lo <<< 3) : BitVec 64) = (hi ++ lo) <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  have h₁ := hi.isLt; have h₂ := lo.isLt
  simp only [Proof.Gcm.toNat_append, BitVec.toNat_shiftLeft, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hor : (hi.toNat * 2 ^ 3 % 2 ^ 32) ||| (lo.toNat / 2 ^ 29) = hi.toNat * 2 ^ 3 % 2 ^ 32 + lo.toNat / 2 ^ 29 := by
    have : lo.toNat / 2 ^ 29 < 2 ^ 3 := by omega
    rw [show hi.toNat * 2 ^ 3 % 2 ^ 32 = 2 ^ 3 * (hi.toNat % 2 ^ 29) by omega, Nat.mul_comm,
      ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt this]
  rw [hor]
  omega

/-- `8 x` modulo 2⁶⁴, as a number. -/
theorem shl3_toNat (x : BitVec 64) : (x <<< 3).toNat = 8 * x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; congr 1; omega

theorem toBytes_append4 (a b c d : BitVec 32) :
    toBytes (a ++ b ++ c ++ d) = be64 (a ++ b).toNat ++ be64 (c ++ d).toNat := by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  have e : (a ++ b ++ c ++ d).toNat = ((a.toNat * 2 ^ 32 + b.toNat) * 2 ^ 32 + c.toNat) * 2 ^ 32 + d.toNat := by
    simp only [Proof.Gcm.toNat_append]
  have e₁ : (a ++ b).toNat = a.toNat * 2 ^ 32 + b.toNat := Proof.Gcm.toNat_append a b
  have e₂ : (c ++ d).toNat = c.toNat * 2 ^ 32 + d.toNat := Proof.Gcm.toNat_append c d
  simp only [toBytes, be64, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true, e₁, e₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, e]
    omega

end VG.Proof.AesGcm.Arm

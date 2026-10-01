import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Rc2.Select

/-! # Word-sized equality masks for SSE2 RC2 scans -/

namespace VG.Proof.Rc2.X86_64.Sse2

private theorem shift_mask (v : BitVec 16) (hb : v.toNat < 256)
    (hn : v.toNat ≠ 0) : (v - 1).sshiftRight 15 = 0 := by
  have hv : (v - 1).toNat = v.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by bv_omega)]
    rfl
  have hs : (v - 1).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, hv]
    omega
  rw [BitVec.sshiftRight_eq_of_msb_false hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, hv]
  rw [Nat.shiftRight_eq_div_pow, show (0 : BitVec 16).toNat = 0 by decide]
  change (v.toNat - 1) / 32768 = 0
  omega

theorem mask_eq (x y : VG.Byte) :
    ((x.setWidth 16 ^^^ y.setWidth 16) - 1).sshiftRight 15 =
      if x = y then BitVec.allOnes 16 else 0 := by
  have hb : (x.setWidth 16 ^^^ y.setWidth 16).toNat < 256 := by
    rw [← BitVec.setWidth_xor]
    simp only [BitVec.toNat_setWidth]
    have h := (x ^^^ y).isLt
    omega
  by_cases h : x = y
  · subst y
    rw [BitVec.xor_self, ite_eq_left rfl]
    decide
  · have hn : x.setWidth 16 ^^^ y.setWidth 16 ≠ 0#16 := by
      intro hz
      have he := BitVec.xor_eq_zero_iff.mp hz
      have he' := congrArg (BitVec.setWidth 8) he
      exact h (by simpa using he')
    have hn' : (x.setWidth 16 ^^^ y.setWidth 16).toNat ≠ 0 := by
      intro hz
      exact hn (BitVec.eq_of_toNat_eq hz)
    rw [ite_eq_right h]
    exact shift_mask _ hb hn'

end VG.Proof.Rc2.X86_64.Sse2

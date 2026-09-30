import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
import VerifiedGarbage.Proof.Framework.Mem

/-!
# ML-DSA: fields of a little-endian word, and subtraction modulo `q`

Untrusted: everything here is checked by Lean. For implementations that
read a field of `c` bits of a byte string `X` as the 32-bit little-endian
word at its first byte, shifted right and masked: the bits of the word from
bit `sh` on are those of `leNat X` from bit `8o + sh` on, if its first
three bytes are those of `X` from byte `o` (`wordBits`). And `(g - x) mod
q`, computed as `g - x` in 32 bits plus `q` masked by the borrow of the
subtraction (`subMask_eq`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- `g - x` modulo `q`, for `x < q + g`: `g - x` in 32 bits, plus `q` masked
by the borrow (`sbb d, d` with `d = x` makes the mask). -/
theorem subMask_eq {g x : BitVec 32} (hg : g.toNat < q) (hx : x.toNat < q + g.toNat) :
    g - x + ((x - x - (BitVec.ofBool (decide (g.toNat < x.toNat))).setWidth 32) &&& 8380417#32) =
      zw (ofInt ((g.toNat : Int) - x.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  rw [zw_toNat]
  simp only [ofInt, Fin.val_ofNat]
  simp only [q] at hg hx ⊢
  by_cases h : g.toNat < x.toNat
  · rw [decide_eq_true h, BitVec.sub_self,
      show (0#32 - BitVec.setWidth 32 (BitVec.ofBool true) &&& 8380417#32) = 8380417#32 by decide,
      BitVec.toNat_add, BitVec.toNat_sub, show (8380417#32).toNat = 8380417 from rfl]
    omega
  · rw [decide_eq_false h, BitVec.sub_self,
      show (0#32 - BitVec.setWidth 32 (BitVec.ofBool false) &&& 8380417#32) = 0 by decide,
      BitVec.toNat_add, BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

/-- Bit `j` of a 32-bit little-endian word. -/
theorem readW32_getLsbD (m : Mem) (a : Addr) {j : Nat} (hj : j < 32) :
    (m.readW a 32).getLsbD j = (m (a + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
  rw [Mem.readW_byte m a (by omega), BitVec.getLsbD_extractLsb']
  simp only [show j % 8 < 8 by omega, decide_true, Bool.true_and]
  congr 1; omega

/-- The `c` bits from bit `sh` of the word at `a` are those of `X` from bit
`8o + sh`, if its first 3 bytes are those of `X` from byte `o`. -/
theorem wordBits (m : Mem) (a : Addr) (X : List Byte) {o sh c : Nat} (hc : sh + c ≤ 24)
    (hb : ∀ b < 3, m (a + BitVec.ofNat 64 b) = X.getD (o + b) 0) :
    (m.readW a 32).toNat / 2 ^ sh % 2 ^ c = leNat X / 2 ^ (8 * o + sh) % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < c
  · simp only [hj, decide_true, Bool.true_and]
    rw [← BitVec.getLsbD, readW32_getLsbD m a (j := j + sh) (by omega), hb ((j + sh) / 8) (by omega),
      testBit_leNat, show (j + (8 * o + sh)) / 8 = o + (j + sh) / 8 by omega,
      show (j + (8 * o + sh)) % 8 = (j + sh) % 8 by omega]
  · simp [hj]

end VG.Proof.MlDsa.Sample

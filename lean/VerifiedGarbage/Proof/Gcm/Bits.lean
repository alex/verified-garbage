import VerifiedGarbage.Proof.Framework.Bswap

/-!
# GHASH: byte reversal of 64-bit halves

Untrusted: everything here is checked by Lean. The GHASH implementations
load the big-endian halves of a block with a byte reversal (`bswap`, `rev`),
and store them back with another: `byteRev64` is an involution.
-/

namespace VG.Proof.Gcm

theorem getLsbD_cat8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (i : Nat) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 :
        BitVec (8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)).getLsbD i =
      if i < 8 then b7.getLsbD i else if i < 16 then b6.getLsbD (i - 8)
      else if i < 24 then b5.getLsbD (i - 16) else if i < 32 then b4.getLsbD (i - 24)
      else if i < 40 then b3.getLsbD (i - 32) else if i < 48 then b2.getLsbD (i - 40)
      else if i < 56 then b1.getLsbD (i - 48) else b0.getLsbD (i - 56) := by
  simp only [BitVec.getLsbD_append]
  simp only [Nat.sub_sub, Nat.reduceAdd]
  by_cases h8 : i < 8; · simp only [h8, ite_true]
  by_cases h16 : i < 16; · simp only [h8, h16, ite_true, ite_false, show i - 8 < 8 by omega]
  by_cases h24 : i < 24
  · simp only [h8, h16, h24, ite_true, ite_false, show ¬ i - 8 < 8 by omega,
      show i - 16 < 8 by omega]
  simp only [h8, h16, h24, ite_false, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega]
  by_cases h32 : i < 32; · simp only [h32, ite_true, show i - 24 < 8 by omega]
  simp only [h32, ite_false, show ¬ i - 24 < 8 by omega]
  by_cases h40 : i < 40; · simp only [h40, ite_true, show i - 32 < 8 by omega]
  simp only [h40, ite_false, show ¬ i - 32 < 8 by omega]
  by_cases h48 : i < 48; · simp only [h48, ite_true, show i - 40 < 8 by omega]
  simp only [h48, ite_false, show ¬ i - 40 < 8 by omega]
  by_cases h56 : i < 56; · simp only [h56, ite_true, show i - 48 < 8 by omega]
  simp only [h56, ite_false, show ¬ i - 48 < 8 by omega]

theorem getLsbD_byteRev64 (a : BitVec 64) (i : Nat) (hi : i < 64) :
    (byteRev64 a).getLsbD i = a.getLsbD (8 * (7 - i / 8) + i % 8) := by
  simp only [byteRev64]
  rw [getLsbD_cat8]
  simp only [BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
    (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ 56 ≤ i) with
    h | h | h | h | h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right] <;>
  (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

theorem byteRev64_byteRev64 (a : BitVec 64) : byteRev64 (byteRev64 a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_byteRev64 _ _ hi, getLsbD_byteRev64 _ _ (by omega)]
  congr 1; omega

end VG.Proof.Gcm

import VerifiedGarbage.Impl.TripleDes.BitsliceLayout

/-!
# Facts about where bitsliced DES keeps each bit

Each fact is about a few small numbers, proved by evaluation.
-/

namespace VG.Proof.TripleDes.Bitslice

open VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice

theorem ipWord_lt : ∀ t < 64, ipWord t < 64 := by decide

theorem ipWord_inj : ∀ t < 64, ∀ u < 64, ipWord t = ipWord u → t = u := by decide +kernel

theorem lWord_lt : ∀ q < 32, lWord q < 64 := by decide
theorem rWord_lt : ∀ q < 32, rWord q < 64 := by decide

theorem lWord_inj : ∀ q < 32, ∀ q' < 32, lWord q = lWord q' → q = q' := by decide +kernel
theorem rWord_inj : ∀ q < 32, ∀ q' < 32, rWord q = rWord q' → q = q' := by decide +kernel
theorem lWord_ne_rWord : ∀ q < 32, ∀ q' < 32, lWord q ≠ rWord q' := by decide +kernel

/-- Every state word is a word of one of the halves. -/
theorem word_cases : ∀ w < 64, (∃ q < 32, w = lWord q) ∨ (∃ q < 32, w = rWord q) := by
  decide +kernel

theorem inBit_lt : ∀ j < 8, ∀ i < 6, inBit j i < 48 := by decide

theorem eBit_lt : ∀ j < 8, ∀ i < 6, eBit (inBit j i) < 32 := by decide

theorem outBit_lt : ∀ j < 8, ∀ i < 4, outBit j i < 32 := by decide

/-- P sends S-box `j`'s output bit `i` to bit `outBit j i` of `f`. -/
theorem outBit_spec : ∀ j < 8, ∀ i < 4, 32 - p.getD (31 - outBit j i) 1 = 4 * (7 - j) + i := by
  decide

theorem outBit_inj' : ∀ x < 32, ∀ y < 32, outBit (x / 4) (x % 4) = outBit (y / 4) (y % 4) → x = y := by
  decide +kernel

theorem outBit_inj {j i j' i' : Nat} (hj : j < 8) (hi : i < 4) (hj' : j' < 8) (hi' : i' < 4)
    (h : outBit j i = outBit j' i') : j = j' ∧ i = i' := by
  have e := outBit_inj' (4 * j + i) (by omega) (4 * j' + i') (by omega)
  have a : (4 * j + i) / 4 = j := by omega
  have b : (4 * j + i) % 4 = i := by omega
  have c : (4 * j' + i') / 4 = j' := by omega
  have d : (4 * j' + i') % 4 = i' := by omega
  rw [a, b, c, d] at e
  have := e h
  omega

theorem outBit_surj : ∀ q < 32, ∃ j < 8, ∃ i < 4, outBit j i = q := by decide +kernel

/-- FP undoes IP: bit `i` of a block, after FP, is in the word of its IP position. -/
theorem fp_ipWord : ∀ i < 64, ipWord (64 - fp.getD (63 - i) 1) = i ^^^ 56 := by decide

theorem fp_bounds : ∀ i < 64, 1 ≤ fp.getD (63 - i) 1 ∧ fp.getD (63 - i) 1 ≤ 64 := by decide
theorem ip_bounds : ∀ t < 64, 1 ≤ ip.getD (63 - t) 1 ∧ ip.getD (63 - t) 1 ≤ 64 := by decide
theorem expansion_bounds : ∀ t < 48, 1 ≤ expansion.getD (47 - t) 1 ∧ expansion.getD (47 - t) 1 ≤ 32 := by
  decide

end VG.Proof.TripleDes.Bitslice

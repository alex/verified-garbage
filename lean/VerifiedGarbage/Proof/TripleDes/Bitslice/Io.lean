import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass

/-!
# Into and out of the bitsliced state, for 64 blocks

64 blocks, as little-endian 64-bit words, are transposed (`transposeW`) so
that word `j` holds bit `j` of every block. Lane `b` of the state is then
IP of block `b` (`ipLane_transpose`), and transposing a state back gives,
in each lane, the little-endian word of FP of its value (`transpose_out`).
-/

namespace VG.Proof.TripleDes.Bitslice

open VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice VG.Bitslice VG.Proof.TripleDes

/-- Bit `b` of word `j` is bit `j` of word `b`. -/
def transposeW (W : Nat → BitVec 64) : Nat → BitVec 64 := fun j => ofBits 64 fun b => (W b).getLsbD j

theorem ipLane_bit {w : Nat} (W : Nat → BitVec w) (b : Nat) {t : Nat} (ht : t < 64) :
    (ipLane W b).getLsbD t = (W (ipWord t)).getLsbD b := by
  simp only [ipLane, BitVec.getLsbD_append]
  by_cases h : t < 32
  · simp only [h, ite_true, half, getLsbD_ofBits, decide_true, Bool.true_and, rWord]
  · have h' : t - 32 < 32 := by omega
    simp only [h, ite_false, half, getLsbD_ofBits, h', decide_true, Bool.true_and, lWord]
    congr 3
    omega

theorem xor56_xor56 (a : Nat) : a ^^^ 56 ^^^ 56 = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- After transposing 64 little-endian blocks, lane `b` is IP of block `b`. -/
theorem ipLane_transpose (W : Nat → BitVec 64) (x : BitVec 64) {b : Nat} (hb : b < 64)
    (hW : ∀ j < 64, (W b).getLsbD j = x.getLsbD (j ^^^ 56)) :
    ipLane (transposeW W) b = permute ip x := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hw := ipWord_lt t ht
  rw [ipLane_bit _ _ ht, permute_bit ip x (by decide) t ht]
  simp only [transposeW, getLsbD_ofBits, hb, decide_true, Bool.true_and, hW _ hw]
  simp only [ipWord, xor56_xor56]

/-- Transposing back: in each lane, the little-endian word of FP of its value. -/
theorem transpose_out (W : Nat → BitVec 64) (b : Nat) :
    ∀ j < 64, (transposeW W b).getLsbD j = (permute fp (ipLane W b)).getLsbD (j ^^^ 56) := by
  intro j hj
  have hj' : j ^^^ 56 < 64 := Nat.xor_lt_two_pow (n := 6) hj (by decide)
  obtain ⟨lo, hi⟩ := fp_bounds _ hj'
  have ht : 64 - fp.getD (63 - (j ^^^ 56)) 1 < 64 := by omega
  rw [permute_bit fp _ (by decide) _ hj', ipLane_bit _ _ ht, fp_ipWord _ hj', xor56_xor56]
  simp only [transposeW, getLsbD_ofBits, hj, decide_true, Bool.true_and]

end VG.Proof.TripleDes.Bitslice

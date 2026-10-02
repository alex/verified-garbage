import VerifiedGarbage.Proof.X448.Wide.Normalize

/-! Untrusted: interpreting the normalized wide output in the original slots. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem decode_encoded (lo hi : BitVec 64) {v : Nat} (h : pair lo hi = encoded v true) :
    lo.toNat = v % VG.Proof.X448.radix ∧ hi.toNat = v / VG.Proof.X448.radix := by
  have hl := lo.isLt
  have hm := Nat.mod_lt v (show 0 < VG.Proof.X448.radix by decide)
  simp only [pair, encoded, ite_true, VG.Proof.X448.radix] at h hm ⊢
  omega

theorem encoded_limbs {m : Mem} {base : Addr} {o : Nat} {f : Nat → Nat}
    (hf : ∀ i < 8, coeff m base o i = encoded (f i) true) :
    ∀ i < 16, limbs m base o i = unpacked f i := by
  intro i hi
  have hq : i / 2 < 8 := by omega
  have dec := decode_encoded _ _ (hf (i / 2) hq)
  have e0 : o + 16 * (i / 2) = o + 8 * (2 * (i / 2)) := by omega
  simp only [e0] at dec
  change limbs m base o (2 * (i / 2)) = _ ∧ limbs m base o (2 * (i / 2) + 1) = _ at dec
  simp only [unpacked]
  split
  · rename_i h
    rw [show i = 2 * (i / 2) from by omega]
    simpa only [show (2 * (i / 2)) / 2 = i / 2 by omega] using dec.1
  · rename_i h
    rw [show i = 2 * (i / 2) + 1 from by omega]
    simpa only [show (2 * (i / 2) + 1) / 2 = i / 2 by omega] using dec.2

end VG.Proof.X448.Wide

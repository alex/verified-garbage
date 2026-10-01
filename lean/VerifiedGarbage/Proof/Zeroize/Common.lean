import VerifiedGarbage.Spec.Zeroize
import VerifiedGarbage.Proof.Framework.Offset

/-! Zero prefixes, shared by the word and byte loops on every target. -/
namespace VG.Proof.Zeroize
open VG

def Prefix (m : Mem) (p : Addr) (n : Nat) : Prop := ∀ j < n, m (p + BitVec.ofNat 64 j) = 0

theorem prefix_spec {m : Mem} {p : Addr} {n : Nat} (h : Prefix m p n) :
    Spec.Zeroize.bytesAt m p n = Spec.Zeroize.zeros n := by
  apply List.eq_replicate_iff.mpr
  refine ⟨by simp [Spec.Zeroize.bytesAt], ?_⟩
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  exact h j (List.mem_range.mp hj)

theorem prefix_write {m : Mem} {p : Addr} {i k : Nat} (h : Prefix m p i)
    (hn : i + k < 2 ^ 64) :
    Prefix (m.write (p + BitVec.ofNat 64 i) k (0 : BitVec (8 * k))) p (i + k) := by
  intro j hj
  unfold Mem.write
  split
  · exact BitVec.extractLsb'_zero
  · rename_i hout
    have hji : j < i := by
      by_contra hh
      rw [Offset.sub_toNat p (by omega) (by omega)] at hout
      omega
    exact h j hji

theorem prefix_writeW {m : Mem} {p : Addr} {i w : Nat} (h : Prefix m p i)
    (hn : i + w / 8 < 2 ^ 64) :
    Prefix (m.writeW (p + BitVec.ofNat 64 i) (0 : BitVec w)) p (i + w / 8) := by
  change Prefix (m.write _ _ _) _ _
  rw [show (0 : BitVec w).setWidth (8 * (w / 8)) = 0 from BitVec.setWidth_zero _ _]
  exact prefix_write h hn
theorem count (x : BitVec 64) : x >>> 3 = BitVec.ofNat 64 (x.toNat / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem tail (x : BitVec 64) : x &&& 7 = BitVec.ofNat 64 (x.toNat % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat]
  omega

end VG.Proof.Zeroize

import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Spec.Ed25519.Contract

/-! The four-word output representation and its memory frame. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 Word64 VG.Proof.X25519

theorem bytesAt_st4 (m : Mem) (q : Addr) (w0 w1 w2 w3 : BitVec 64) :
    Spec.X25519.bytesAt (st4 m q 0 w0 w1 w2 w3) q 32 = leBytes 32 (val4 w0 w1 w2 w3) := by
  have e : ((st4 m q 0 w0 w1 w2 w3).readW (off q 0) 64).toNat +
      2 ^ 64 * ((st4 m q 0 w0 w1 w2 w3).readW (q + 8) 64).toNat +
      2 ^ 128 * ((st4 m q 0 w0 w1 w2 w3).readW (q + 16) 64).toNat +
      2 ^ 192 * ((st4 m q 0 w0 w1 w2 w3).readW (q + 24) 64).toNat = val4 w0 w1 w2 w3 :=
    fe_st4 m q (by decide) w0 w1 w2 w3
  rw [show off q 0 = q from BitVec.add_zero q] at e
  have := ((st4 m q 0 w0 w1 w2 w3).readW q 64).isLt
  have := ((st4 m q 0 w0 w1 w2 w3).readW (q + 8) 64).isLt
  have := ((st4 m q 0 w0 w1 w2 w3).readW (q + 16) 64).isLt
  have := ((st4 m q 0 w0 w1 w2 w3).readW (q + 24) 64).isLt
  exact bytesAt_leBytes_words64 _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem scalarSave_frame {base : Addr} {m m' : Mem} (h : Outside base 0 48 m m') :
    Frame [⟨base, 8192⟩] m m' := by
  intro x hx
  apply h x
  right
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  simp only [ofs]
  omega

theorem bytesAt_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 64⟩ : Region).Disjoint ⟨base, 8192⟩) :
    Spec.Ed25519.bytesAt m' p 64 = Spec.Ed25519.bytesAt m p 64 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 64⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

theorem encodeLE_eq (n x : Nat) : Spec.Ed25519.encodeLE n x = leBytes n x := by
  simp only [Spec.Ed25519.encodeLE, leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

end VG.Proof.Ed25519.AArch64

import VerifiedGarbage.Proof.Framework.AArch64.Simd

namespace VG.AArch64

/-- EXT of a vector with itself rotates its packed 32-bit lanes. -/
theorem vword_ext_rotate (x : BitVec 128) (k e : Nat) (hk : k < 4) (he : e < 4) :
    vword (((x ++ x) >>> (4 * k * 8)).extractLsb' 0 128) e =
      vword x ((e + k) % 4) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_ushiftRight,
    hi,decide_true,Bool.true_and,Nat.zero_add,
    show 32 * e + i < 128 by omega,BitVec.getLsbD_append]
  split
  · exact congrArg x.getLsbD (by omega)
  · exact congrArg x.getLsbD (by omega)

end VG.AArch64

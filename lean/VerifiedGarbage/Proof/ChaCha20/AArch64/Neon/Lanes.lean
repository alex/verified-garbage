import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.ChaCha20.Spec

namespace VG.Proof.ChaCha20.AArch64.Neon

open VG VG.AArch64

theorem vword_xor (x y : BitVec 128) (e : Nat) :
    vword (x ^^^ y) e = vword x e ^^^ vword y e := by
  simp only [vword, BitVec.extractLsb'_xor]

/-- The insert mask retains exactly the low bits supplied by USHR. -/
theorem shr_mask (x : BitVec 32) (k : Nat) (hk : k < 32) :
    (x >>> (32 - k)) &&& ~~~(BitVec.allOnes 32 <<< k) = x >>> (32 - k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < k
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      hi, h, decide_true, Bool.not_true, Bool.false_and, Bool.not_false,
      Bool.true_and, Bool.and_true]
  · have hx : x.getLsbD (32 - k + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, hx, Bool.false_and]

theorem sli_ushr (x : BitVec 32) (k : Nat) (hk : k < 32) :
    VShiftOp.sli.eval k 32 (x >>> (32 - k)) x = x.rotateLeft k := by
  rw [VShiftOp.eval, shr_mask x k hk, BitVec.rotateLeft_def, Nat.mod_eq_of_lt hk,
    BitVec.or_comm]

/-- EXT aligns the rows for the four parallel diagonal quarter rounds. -/
theorem vword_ext (x : BitVec 128) (k e : Nat) (hk : k < 4) (he : e < 4) :
    vword (((x ++ x) >>> (4 * k * 8)).extractLsb' 0 128) e =
      vword x ((e + k) % 4) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and, Nat.zero_add,
    show 32 * e + i < 128 by omega, BitVec.getLsbD_append]
  split
  · exact congrArg x.getLsbD (by omega)
  · exact congrArg x.getLsbD (by omega)

end VG.Proof.ChaCha20.AArch64.Neon

import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha3.AArch64.Permute

namespace VG.Proof.Sha3.AArch64.Sha3

open VG VG.AArch64

theorem low_xor (a b : BitVec 128) :
    vdword (a ^^^ b) 0 = vdword a 0 ^^^ vdword b 0 := by
  simp only [vdword, BitVec.extractLsb'_xor]

theorem low_and (a b : BitVec 128) :
    vdword (a &&& b) 0 = vdword a 0 &&& vdword b 0 := by
  simp only [vdword, BitVec.extractLsb'_and]

theorem low_not (a : BitVec 128) : vdword (~~~a) 0 = ~~~(vdword a 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, Nat.mul_zero,
    Nat.zero_add, hi, decide_true, Bool.true_and, show i < 128 by omega]

theorem low_ext8 (a : BitVec 128) :
    vdword (((a ++ a) >>> (8 * 8)).extractLsb' 0 128) 0 = vdword a 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, Nat.mul_zero, Nat.zero_add, Nat.mul_one, hi,
    show i < 128 by omega, show 8 * 8 + i < 128 by omega,
    decide_true, Bool.true_and, ite_true]

theorem exec_vop (s : VG.AArch64.State) (op : VOp) :
    exec (.vop op) s = (VOp.eval s op).map (fun p => s.setV p.1 p.2) := rfl

theorem chi_low (a b c : BitVec 128) :
    vdword (a ^^^ (c &&& ~~~b)) 0 =
      (vdword b 0 ^^^ 0xffffffffffffffff) &&& vdword c 0 ^^^ vdword a 0 := by
  rw [low_xor, low_and, low_not]
  change _ = (vdword b 0 ^^^ BitVec.allOnes 64) &&& vdword c 0 ^^^ vdword a 0
  rw [BitVec.xor_allOnes, BitVec.and_comm, BitVec.xor_comm]

theorem chi_xor_low (a b c r : BitVec 128) :
    vdword ((a ^^^ (c &&& ~~~b)) ^^^ r) 0 =
      ((vdword b 0 ^^^ 0xffffffffffffffff) &&& vdword c 0 ^^^ vdword a 0) ^^^ vdword r 0 := by
  rw [low_xor, chi_low]

theorem rotl_mod (a : BitVec 64) (k : Nat) (hk : k < 64) :
    a.rotateRight ((64 - k) % 64) = Proof.Sha3.rotl a k := by
  by_cases h : k = 0
  · subst h
    simp only [Proof.Sha3.rotl, Nat.sub_zero, Nat.mod_self, ite_true]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  · simp only [Proof.Sha3.rotl, h, ite_false, Nat.mod_eq_of_lt (by omega : 64 - k < 64)]

theorem exec_umov_low (s : VG.AArch64.State) (d : Reg) (n : VReg) :
    exec (.umov .x d n 0) s = some (s.write .x d (vdword (s.v n) 0)) := rfl

end VG.Proof.Sha3.AArch64.Sha3

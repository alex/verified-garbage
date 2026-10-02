import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Vector
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
set_option linter.unusedSimpArgs false

theorem sli_rotate (x : BitVec 64) {k : Nat} (hk : k < 64) :
    VShiftOp.sli.eval k 64 (x >>> (64-k)) x = x.rotateLeft k := by
  rw [VShiftOp.eval,BitVec.rotateLeft_def,Nat.mod_eq_of_lt hk,BitVec.or_comm (x <<< k)]
  apply congrArg (· ||| (x <<< k))
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes,BitVec.getLsbD_ushiftRight]
  by_cases h : i < k
  · simp only [hi,h,decide_true,decide_false,Bool.true_and,Bool.false_and,
      Bool.and_true,Bool.not_true,Bool.not_false,Bool.and_false]
  · rw [BitVec.getLsbD_of_ge x (64-k+i) (by omega : 64 ≤ 64-k+i)]
    simp only [Bool.false_and]

theorem rol_ok {s : State} {d n : VReg} (hdn : d ≠ n) {k : Nat} (hk0 : 0 < k) (hk : k < 64) :
    WP isa (.block (rol d n k)) s fun s' => VChg [d] s s' ∧
      s'.v d = ofVDwords ((vdword (s.v n) 0).rotateLeft k) ((vdword (s.v n) 1).rotateLeft k) := by
  unfold rol
  refine wp_vop (op := .shift .ushr .d2 d n (64-k)) (d := d)
    (x := VArr.d2.map2 (fun w a b => VShiftOp.ushr.eval (64-k) w a b) (s.v d) (s.v n))
    (by simp [VOp.eval,VShiftOp.ok,show 1 ≤ 64-k by omega,show 64-k ≤ 64 by omega]) fun s₁ h1 => ?_
  refine wp_vop (op := .shift .sli .d2 d n k) (d := d)
    (x := VArr.d2.map2 (fun w a b => VShiftOp.sli.eval k w a b) (s₁.v d) (s₁.v n))
    (by simp [VOp.eval,VShiftOp.ok,hk]) fun s₂ h2 => WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (by intro r hr; simpa using hr),?_⟩
  rw [h2.v,h1.v,h1.get n (Ne.symm hdn)]
  simp only [VArr.map2,vdword_ofVDwords_0,vdword_ofVDwords_1,VShiftOp.eval]
  change ofVDwords (VShiftOp.sli.eval k 64 ((vdword (s.v n) 0) >>> (64-k)) (vdword (s.v n) 0))
    (VShiftOp.sli.eval k 64 ((vdword (s.v n) 1) >>> (64-k)) (vdword (s.v n) 1)) = _
  rw [sli_rotate _ hk,sli_rotate _ hk]
end VG.Proof.Sha3.AArch64.Neon

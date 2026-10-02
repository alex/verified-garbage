import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha224

/-!
# PBKDF2-HMAC-SHA-224 on 32-bit ARM, the whole derivation

The generic proof (`CT.lean`) at SHA-224
(`Proof/Hmac/Generic/Arm/Sha224.lean`), as for the other hash functions
(`Instances.lean`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Proof.Hmac.Generic.Arm (sha224H sha224OK)

def sha224F : Fns := fnsOf Spec.Hmac.sha224I Md.Arm.sha224Md

theorem sha224_checks : Checks sha224F := by
  constructor <;> exact ⟨_, by taint_decide⟩

def sha224OKF : FnsOK sha224F where
  hH := sha224OK
  Wi := 104
  Wf := 104
  Wt := 104
  hi := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha224_init
  hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha224_finalize
  it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha224_iterate
  hiSt := by decide +kernel
  hfSt := by decide +kernel
  itSt := by decide +kernel
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide
  reach := by decide
  encB1 := by decide
  encB := by decide
  encB4 := by decide
  encD := by decide

theorem sha224_sat : ∃ s, (Spec.Hmac.sha224I.pbkdf2Contract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using pbkSat 200

theorem sha224 : Verified Arm.target sha224F.pbkdf2 (Spec.Hmac.sha224I.pbkdf2Contract Arm.abi 24) :=
  verified sha224OKF sha224_checks rfl rfl sha224_sat

end VG.Proof.Pbkdf2.Whole.Arm

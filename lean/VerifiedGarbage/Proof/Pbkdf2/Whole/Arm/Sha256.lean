import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha256

/-!
# PBKDF2-HMAC-SHA-256 on 32-bit ARM, the whole derivation

The generic proof (`CT.lean`) at SHA-256
(`Proof/Hmac/Generic/Arm/Sha256.lean`), as for the other hash functions
(`Instances.lean`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Proof.Hmac.Generic.Arm (sha256OK)

def sha256F : Fns := fnsOf Spec.Hmac.sha256I Md.Arm.sha256Md

theorem sha256_checks : Checks sha256F := by
  constructor <;> exact ⟨_, by taint_decide⟩

def sha256OKF : FnsOK sha256F where
  hH := sha256OK
  Wi := 104
  Wf := 104
  Wt := 104
  hi := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha256_init
  hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha256_finalize
  it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha256_iterate
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

theorem sha256_sat : ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using pbkSat 200

theorem sha256 : Verified Arm.target sha256F.pbkdf2 (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24) :=
  verified sha256OKF sha256_checks rfl rfl sha256_sat

end VG.Proof.Pbkdf2.Whole.Arm

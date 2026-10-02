import VerifiedGarbage.Proof.Pbkdf2.Generic.Arm.Instances
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Sha224

/-!
# The PBKDF2-HMAC-SHA-224 iteration on 32-bit ARM

Untrusted: everything here is checked by Lean. The generic proof of the
iteration (`Instances.lean`) at SHA-224 (`Proof/Hmac/Generic/Arm/Sha224.lean`),
moved to the shared contract of `Spec.Hmac.sha224I`.
-/

namespace VG.Proof.Pbkdf2.Generic.Arm.Instances

open VG.Arm
open VG.Proof.Hmac.Generic.Arm
open VG.Proof.Pbkdf2.Generic.Arm

theorem sha224_checks : Checks sha224H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha224_imp : (iterG Spec.Hmac.sha224S 104).Implies (Spec.Hmac.sha224I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha224S 104 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha224S, Spec.Hmac.sha224, iterG,
      below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 96 28 104)

theorem sha224 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha224H)
    (Spec.Hmac.sha224I.iterateContract Arm.abi 16) :=
  (verified sha224OK sha224_checks (by decide) sha224_imp.sat_left).of_implies sha224_imp

end VG.Proof.Pbkdf2.Generic.Arm.Instances

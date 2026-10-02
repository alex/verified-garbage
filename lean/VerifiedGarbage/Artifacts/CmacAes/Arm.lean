import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.CmacAes.Arm.Verified

/-!
# AES-CMAC (NIST SP 800-38B) on ARMv7

Each function calls `vg_aes_ctr32` in a frame that pushes its two stack
arguments, so uses 8 bytes of stack.
-/

namespace VG.Artifacts.CmacAes.Arm

open VG.Proof.CmacAes.Arm

/-- How the functions encrypt a block. -/
def ctrNote : String := "This implementation encrypts each block with `vg_aes_ctr32`."

def artifacts : List Artifact := [
  { Spec.Cmac.aesSubkeysApi with
    target := Arm.target
    doc := Spec.Cmac.aesSubkeysApi.doc (notes := [ctrNote])
    code := Impl.CmacAes.Arm.subkeys
    contract := Spec.Cmac.aesSubkeysContract Arm.abi 8
    stack := 8
    verified := subkeys_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.aesUpdateApi with
    target := Arm.target
    doc := Spec.Cmac.aesUpdateApi.doc (notes := [ctrNote])
    code := Impl.CmacAes.Arm.update
    contract := Spec.Cmac.aesUpdateContract Arm.abi 8
    stack := 8
    verified := update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.aesFinalizeApi with
    target := Arm.target
    doc := Spec.Cmac.aesFinalizeApi.doc (notes := [ctrNote])
    code := Impl.CmacAes.Arm.finalize
    contract := Spec.Cmac.aesFinalizeContract Arm.abi 8
    stack := 8
    verified := finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CmacAes.Arm

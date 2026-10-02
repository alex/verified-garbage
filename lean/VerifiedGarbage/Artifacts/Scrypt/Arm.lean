import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Scrypt.Arm.Salsa
import VerifiedGarbage.Impl.Scrypt.Arm.BlockMix
import VerifiedGarbage.Impl.Scrypt.Arm.RoMix
import VerifiedGarbage.Proof.Scrypt.Arm.BlockMixVerified
import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
import VerifiedGarbage.Proof.Scrypt.Arm.Lit

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on 32-bit ARM
-/

namespace VG.Artifacts.Scrypt.Arm

def artifacts : List Artifact := [
  { Spec.Scrypt.salsaApi with
    target := Arm.target
    doc := Spec.Scrypt.salsaApi.doc
    code := Impl.Scrypt.Arm.salsa
    contract := Spec.Scrypt.salsaContract Arm.abi
    verified := Proof.Scrypt.Arm.salsa_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.blockMixApi with
    target := Arm.target
    doc := Spec.Scrypt.blockMixApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Scrypt.Arm.blockMix
    contract := Spec.Scrypt.blockMixContract Arm.abi
    verified := Proof.Scrypt.Arm.BlockMix.blockMix_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.roMixApi with
    target := Arm.target
    doc := Spec.Scrypt.roMixApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Scrypt.Arm.roMix
    contract := Spec.Scrypt.roMixContract Arm.abi
    verified := Proof.Scrypt.Arm.RoMix.roMix_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Scrypt.Arm

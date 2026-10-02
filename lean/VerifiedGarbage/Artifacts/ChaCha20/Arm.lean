import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.ChaCha20.Arm.Xor
import VerifiedGarbage.Impl.ChaCha20.Arm.Xor
import VerifiedGarbage.Proof.ChaCha20.Arm.Lit

/-! # The ChaCha20 block function (RFC 8439) on ARMv7 -/

namespace VG.Artifacts.ChaCha20.Arm

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := Arm.target
    doc := Spec.ChaCha20.blockApi.doc
    code := Impl.ChaCha20.Arm.block
    contract := Spec.ChaCha20.blockContract Arm.abi
    verified := Proof.ChaCha20.Arm.block_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.xorApi with
    target := Arm.target
    doc := Spec.ChaCha20.xorApi.doc (notes := ["Calls `vg_chacha20_block` for each 64 bytes."])
    code := Impl.ChaCha20.Arm.Xor.xor
    contract := Spec.ChaCha20.xorContract Arm.abi
    verified := Proof.ChaCha20.Arm.Xor.xor_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20.Arm

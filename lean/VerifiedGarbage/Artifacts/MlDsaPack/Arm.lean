import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintPackCT
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpackCT

/-! # ML-DSA (FIPS 204) on 32-bit ARM: the encodings -/

namespace VG.Artifacts.MlDsaPack.Arm

def artifacts : List Artifact := [
  { Spec.MlDsa.simpleBitPackApi with
    target := Arm.target
    doc := Spec.MlDsa.simpleBitPackApi.doc
    code := Impl.MlDsa.Arm.Pack.simpleBitPack
    contract := Spec.MlDsa.simpleBitPackContract Arm.abi
    verified := Proof.MlDsa.Arm.Pack.simpleBitPack_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.bitPackApi with
    target := Arm.target
    doc := Spec.MlDsa.bitPackApi.doc
      (notes := ["The function saves `r4` in a frame of 4 bytes on the stack, below the stack pointer."])
    code := Impl.MlDsa.Arm.Pack.bitPack
    contract := Spec.MlDsa.bitPackContract Arm.abi 4
    stack := 4
    verified := Proof.MlDsa.Arm.Pack.bitPack_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.bitUnpackApi with
    target := Arm.target
    doc := Spec.MlDsa.bitUnpackApi.doc
      (notes := ["The function saves `r4` in a frame of 4 bytes on the stack, below the stack pointer."])
    code := Impl.MlDsa.Arm.Pack.bitUnpack
    contract := Spec.MlDsa.bitUnpackContract Arm.abi 4
    stack := 4
    verified := Proof.MlDsa.Arm.Pack.bitUnpack_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.unpackT1Api with
    target := Arm.target
    doc := Spec.MlDsa.unpackT1Api.doc
    code := Impl.MlDsa.Arm.Pack.unpackT1
    contract := Spec.MlDsa.unpackT1Contract Arm.abi
    verified := Proof.MlDsa.Arm.Pack.unpackT1_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.hintBitPackApi with
    target := Arm.target
    doc := Spec.MlDsa.hintBitPackApi.doc
      (notes := ["The function saves `r4` and `r5` in a frame of 8 bytes on the stack, below the stack pointer."])
    code := Impl.MlDsa.Arm.Pack.hintBitPack
    contract := Spec.MlDsa.hintBitPackContract Arm.abi 8
    stack := 8
    verified := Proof.MlDsa.Arm.Pack.Hint.hintBitPack_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.hintBitUnpackApi with
    target := Arm.target
    doc := Spec.MlDsa.hintBitUnpackApi.doc
      (notes := ["The function saves `r4`–`r7` in a frame of 16 bytes on the stack, below the stack pointer."])
    code := Impl.MlDsa.Arm.Pack.hintBitUnpack
    contract := Spec.MlDsa.hintBitUnpackContract Arm.abi 16
    stack := 16
    verified := Proof.MlDsa.Arm.Pack.Hint.hintBitUnpack_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaPack.Arm

import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlKem1024.Arm.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.Arm.Decompress
import VerifiedGarbage.Proof.MlKem1024.Arm.CheckEk
import VerifiedGarbage.Proof.MlKem1024.Arm.KeyGenCT
import VerifiedGarbage.Proof.MlKem1024.Arm.EncapsCT
import VerifiedGarbage.Proof.MlKem1024.Arm.DecapsCT

/-! # ML-KEM-1024 (FIPS 203) on 32-bit ARM -/

namespace VG.Artifacts.MlKem1024.Arm

def artifacts : List Artifact := [
  { Spec.MlKem1024.compressEncodeApi with
    target := Arm.target
    doc := Spec.MlKem1024.compressEncodeApi.doc
    code := Impl.MlKem1024.Arm.compressEncode1024
    contract := Spec.MlKem1024.compressEncodeContract Arm.abi
    verified := Proof.MlKem1024.Arm.CompressEncode.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.decodeDecompressApi with
    target := Arm.target
    doc := Spec.MlKem1024.decodeDecompressApi.doc
    code := Impl.MlKem1024.Arm.decodeDecompress1024
    contract := Spec.MlKem1024.decodeDecompressContract Arm.abi
    verified := Proof.MlKem1024.Arm.Decompress.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.checkEkApi with
    target := Arm.target
    doc := Spec.MlKem1024.checkEkApi.doc
    code := Impl.MlKem1024.Arm.checkEk1024
    contract := Spec.MlKem1024.checkEkContract Arm.abi
    verified := Proof.MlKem1024.Arm.CheckEk.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.keyGenApi with
    target := Arm.target
    doc := Spec.MlKem1024.keyGenApi.doc
      (notes := ["The function saves `r4`–`r11` and its return address in `scratch`; the 8 bytes of stack \
        below the stack pointer hold the stack arguments of the SHA-3 functions it calls."])
    code := Impl.MlKem1024.Arm.keygen1024
    contract := Spec.MlKem1024.keyGenContract Arm.abi 8
    stack := 8
    verified := Proof.MlKem1024.Arm.KeyGen.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.encapsApi with
    target := Arm.target
    doc := Spec.MlKem1024.encapsApi.doc
      (notes := ["The function saves `r4`–`r11` and its return address in `scratch`, and copies `m` into it; \
        the 8 bytes of stack below the stack pointer hold the stack arguments of the SHA-3 functions it calls."])
    code := Impl.MlKem1024.Arm.encaps1024
    contract := Spec.MlKem1024.encapsContract Arm.abi 8
    stack := 8
    verified := Proof.MlKem1024.Arm.Encaps.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.decapsApi with
    target := Arm.target
    doc := Spec.MlKem1024.decapsApi.doc
      (notes := ["The function saves `r4`–`r11`, its return address and `key` in `scratch`, and copies `ct` \
        into it; the 8 bytes of stack below the stack pointer hold the stack arguments of the SHA-3 functions it \
        calls."])
    code := Impl.MlKem1024.Arm.decaps1024
    contract := Spec.MlKem1024.decapsContract Arm.abi 8
    stack := 8
    verified := Proof.MlKem1024.Arm.Decaps.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlKem1024.Arm

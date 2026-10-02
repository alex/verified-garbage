import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlKem1024.AArch64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.AArch64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.AArch64.CheckEk
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps

/-! # ML-KEM-1024 on AArch64 -/

namespace VG.Artifacts.MlKem1024.AArch64

def artifacts : List Artifact := [
  { Spec.MlKem1024.compressEncodeApi with
    target := AArch64.target
    doc := Spec.MlKem1024.compressEncodeApi.doc
    code := Impl.MlKem1024.AArch64.compressEncode
    contract := Spec.MlKem1024.compressEncodeContract AArch64.abi
    verified := Proof.MlKem1024.AArch64.CE.compressEncode_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.decodeDecompressApi with
    target := AArch64.target
    doc := Spec.MlKem1024.decodeDecompressApi.doc
    code := Impl.MlKem1024.AArch64.decodeDecompress
    contract := Spec.MlKem1024.decodeDecompressContract AArch64.abi
    verified := Proof.MlKem1024.AArch64.DD.decodeDecompress_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.checkEkApi with
    target := AArch64.target
    doc := Spec.MlKem1024.checkEkApi.doc
    code := Impl.MlKem1024.AArch64.checkEk
    contract := Spec.MlKem1024.checkEkContract AArch64.abi
    verified := Proof.MlKem1024.AArch64.CheckEk.checkEk_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlKem1024.AArch64

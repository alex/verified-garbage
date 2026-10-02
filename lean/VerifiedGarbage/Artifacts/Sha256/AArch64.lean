import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha256.AArch64.Shared
import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Compress

/-! # SHA-256 (FIPS 180-4) on AArch64 -/

namespace VG.Artifacts.Sha256.AArch64

def artifacts : List Artifact := [
  { Spec.Sha256.compressApi with
    target := AArch64.target
    doc := Spec.Sha256.compressApi.doc
    code := Impl.Sha256.AArch64.compress
    contract := Spec.Sha256.compressContract AArch64.abi
    verified := Proof.Sha256.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha256.initApi with
    target := AArch64.target
    doc := Spec.Sha256.initApi.doc
    code := Impl.Sha256.AArch64.Stream.init
    contract := Spec.Sha256.initContract AArch64.abi
    verified := Proof.Sha256.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha256.compressApi with
    name := "vg_sha256_compress_sha2"
    target := AArch64.target
    doc := Spec.Sha256.compressApi.doc (notes := ["Uses the AArch64 SHA-256 instructions."])
    code := Impl.Sha256.AArch64.Sha2.compress
    contract := Spec.Sha256.compressContract AArch64.abi
    verified := Proof.Sha256.AArch64.Shared.compress_of Proof.Sha256.AArch64.Sha2.compress_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := ["sha2"] }]

end VG.Artifacts.Sha256.AArch64

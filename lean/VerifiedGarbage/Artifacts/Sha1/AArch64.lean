import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha1.AArch64.Shared
import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Compress

/-! # SHA-1 (FIPS 180-4) on AArch64 -/

namespace VG.Artifacts.Sha1.AArch64

def artifacts : List Artifact := [
  { Spec.Sha1.compressApi with
    target := AArch64.target
    doc := Spec.Sha1.compressApi.doc
    code := Impl.Sha1.AArch64.compress
    contract := Spec.Sha1.compressContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.initApi with
    target := AArch64.target
    doc := Spec.Sha1.initApi.doc
    code := Impl.Sha1.AArch64.Stream.init
    contract := Spec.Sha1.initContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.compressApi with
    name := "vg_sha1_compress_sha2"
    target := AArch64.target
    doc := Spec.Sha1.compressApi.doc (notes := ["Uses the AArch64 SHA-1 instructions."])
    code := Impl.Sha1.AArch64.Sha2.compress
    contract := Spec.Sha1.compressContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.compress_of Proof.Sha1.AArch64.Sha2.compress_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := ["sha2"] }]

end VG.Artifacts.Sha1.AArch64

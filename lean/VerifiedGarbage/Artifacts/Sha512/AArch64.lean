import VerifiedGarbage.Proof.Sha512.AArch64.Sha3Backend
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha512.AArch64.Shared

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on AArch64 -/

namespace VG.Artifacts.Sha512.AArch64

def artifacts : List Artifact := [
  { Spec.Sha512.compressApi with
    target := AArch64.target
    doc := Spec.Sha512.compressApi.doc
    code := Impl.Sha512.AArch64.compress
    contract := Spec.Sha512.compressContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init384Api with
    target := AArch64.target
    doc := Spec.Sha512.init384Api.doc
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_384
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512Api with
    target := AArch64.target
    doc := Spec.Sha512.init512Api.doc
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512_224Api with
    target := AArch64.target
    doc := Spec.Sha512.init512_224Api.doc
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512_224
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512_256Api with
    target := AArch64.target
    doc := Spec.Sha512.init512_256Api.doc
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512_256
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.compressApi with
    name := "vg_sha512_compress_sha3"
    target := AArch64.target
    doc := Spec.Sha512.compressApi.doc (notes := ["Uses the AArch64 SHA-512 instructions \
      (FEAT_SHA512)."])
    code := Impl.Sha512.AArch64.Sha3.compress
    contract := Spec.Sha512.compressContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.compress_of Proof.Sha512.AArch64.Sha3.compress_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := ["sha3"] }]

end VG.Artifacts.Sha512.AArch64

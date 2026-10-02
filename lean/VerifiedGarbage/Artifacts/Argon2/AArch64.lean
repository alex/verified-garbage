import VerifiedGarbage.Proof.Argon2.AArch64.Compress

/-! Argon2 block compression on baseline ARM64. -/
namespace VG.Artifacts.Argon2.AArch64

def artifacts : List Artifact := [
  { Spec.Argon2.compressApi with
    target := AArch64.target
    doc := Spec.Argon2.compressApi.doc
    code := Impl.Argon2.AArch64.compress
    contract := Spec.Argon2.compressContract AArch64.abi
    stack := 0
    verified := Proof.Argon2.AArch64.compress_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]
end VG.Artifacts.Argon2.AArch64

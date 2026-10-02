import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha256.AArch64.Shared

/-!
# SHA-224 (FIPS 180-4) on AArch64

SHA-224 is SHA-256 from another initial hash value: only its `init` is its
own, and it continues with SHA-256's `update` and `finalize`
(`Artifacts/Sha256/`).
-/

namespace VG.Artifacts.Sha224.AArch64

def artifacts : List Artifact := [
  { Spec.Sha256.init224Api with
    target := AArch64.target
    doc := Spec.Sha256.init224Api.doc
    code := Impl.Sha256.AArch64.Stream.init224
    contract := Spec.Sha256.init224Contract AArch64.abi
    verified := Proof.Sha256.AArch64.Shared.init224
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha224.AArch64

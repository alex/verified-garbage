import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha256.Arm.Shared

/-!
# SHA-224 (FIPS 180-4) on ARMv7

SHA-224 is SHA-256 from another initial hash value: only its `init` is its
own, and it continues with SHA-256's `update` and `finalize`
(`Artifacts/Sha256/`).
-/

namespace VG.Artifacts.Sha224.Arm

def artifacts : List Artifact := [
  { Spec.Sha256.init224Api with
    target := Arm.target
    doc := Spec.Sha256.init224Api.doc
    code := Impl.Sha256.Arm.Stream.init224
    contract := Spec.Sha256.init224Contract Arm.abi
    verified := Proof.Sha256.Arm.Shared.init224
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha224.Arm

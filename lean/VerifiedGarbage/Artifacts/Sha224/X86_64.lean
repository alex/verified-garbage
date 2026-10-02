import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha256.X86_64.Shared

/-!
# SHA-224 (FIPS 180-4) on x86-64

SHA-224 is SHA-256 from another initial hash value: only its `init` is its
own, and it continues with SHA-256's `update` and `finalize`
(`Artifacts/Sha256/`).
-/

namespace VG.Artifacts.Sha224.X86_64

def artifacts : List Artifact := [
  { Spec.Sha256.init224Api with
    target := X86_64.target
    doc := Spec.Sha256.init224Api.doc
    code := Impl.Sha256.X86_64.Stream.init224
    contract := Spec.Sha256.init224Contract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.init224
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha224.X86_64

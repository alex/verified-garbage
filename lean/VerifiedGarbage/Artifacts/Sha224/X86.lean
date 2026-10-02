import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Shared

/-!
# SHA-224 (FIPS 180-4) on x86 (32-bit)

SHA-224 is SHA-256 from another initial hash value: only its `init` is its
own, and it continues with SHA-256's `update` and `finalize`
(`Artifacts/Sha256/`).
-/

namespace VG.Artifacts.Sha224.X86

def artifacts : List Artifact := [
  { Spec.Sha256.init224Api with
    target := X86.target
    doc := Spec.Sha256.init224Api.doc
    code := Impl.Sha256.X86.Stream.init224
    contract := Spec.Sha256.init224Contract X86.abi
    verified := Proof.Sha256.X86.Shared.init224
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha224.X86

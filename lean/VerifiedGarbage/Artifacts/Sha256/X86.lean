import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Shared

/-! # SHA-256 (FIPS 180-4) on x86 -/

namespace VG.Artifacts.Sha256.X86

def artifacts : List Artifact := [
  { Spec.Sha256.initApi with
    target := X86.target
    doc := Spec.Sha256.initApi.doc
    code := Impl.Sha256.X86.Stream.init
    contract := Spec.Sha256.initContract X86.abi
    verified := Proof.Sha256.X86.Shared.init
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha256.X86

import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Selftest.X86_64
import VerifiedGarbage.Proof.Selftest.X86_64

/-! # The pipeline self-test on x86-64 -/

namespace VG.Artifacts.Selftest.X86_64

def artifacts : List Artifact := [
  { Spec.Selftest.addApi with
    target := X86_64.target
    doc := Spec.Selftest.addApi.summary
    code := Impl.Selftest.X86_64.add
    contract := Spec.Selftest.addContract X86_64.abi
    verified := Proof.Selftest.X86_64.add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Selftest.X86_64

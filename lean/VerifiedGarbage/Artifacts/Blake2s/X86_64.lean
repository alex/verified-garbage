import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified

/-! # BLAKE2s (RFC 7693) on x86-64 -/

namespace VG.Artifacts.Blake2s.X86_64

def artifacts : List Artifact := [
  { Spec.Blake2.compressSApi with
    target := X86_64.target
    doc := Spec.Blake2.compressSApi.doc
    code := Impl.Blake2.X86_64.compress Spec.Blake2.s
    contract := Spec.Blake2.compressSContract X86_64.abi
    verified := Proof.Blake2.X86_64.compressS_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.initSApi with
    target := X86_64.target
    doc := Spec.Blake2.initSApi.doc
    code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.s
    contract := Spec.Blake2.initSContract X86_64.abi
    verified := Proof.Blake2.X86_64.Stream.initS_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.updateSApi with
    target := X86_64.target
    doc := Spec.Blake2.updateSApi.doc
    code := Impl.Blake2.X86_64.Stream.update Spec.Blake2.s
    contract := Spec.Blake2.updateSContract X86_64.abi 8
    stack := 8
    verified := Proof.Blake2.X86_64.Stream.updateS_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.finalizeSApi with
    target := X86_64.target
    doc := Spec.Blake2.finalizeSApi.doc
    code := Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s
    contract := Spec.Blake2.finalizeSContract X86_64.abi 8
    stack := 8
    verified := Proof.Blake2.X86_64.Stream.finalizeS_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Blake2s.X86_64

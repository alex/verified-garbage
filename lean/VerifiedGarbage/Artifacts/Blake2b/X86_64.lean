import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified

/-!
# BLAKE2b (RFC 7693) on x86-64

The backend-independent initialization function. Compression and streaming
callers are registered through `Variants/Blake2b/X86_64/` and
`Generic/Blake2b/X86_64/Stream.lean`.
-/

namespace VG.Artifacts.Blake2b.X86_64

def artifacts : List Artifact := [
  { Spec.Blake2.initBApi with
    target := X86_64.target
    doc := Spec.Blake2.initBApi.doc
    code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.b
    contract := Spec.Blake2.initBContract X86_64.abi
    verified := Proof.Blake2.X86_64.Stream.initB_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Blake2b.X86_64

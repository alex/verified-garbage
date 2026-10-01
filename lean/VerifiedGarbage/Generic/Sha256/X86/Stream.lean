import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-! Generic stream registrations for every x86 SHA-256 backend. -/

namespace VG.Generic.Sha256.X86.Stream

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := v.functions.map fun f =>
  { f.api with
    name := f.api.name ++ v.suffix
    target := X86.target
    doc := f.api.doc
    code := f.code
    contract := f.contract
    stack := f.stack
    verified := f.verified
    ofSig := f.ofSig
    ofApi := f.ofApi
    spSafe := f.spSafe
    features := v.features }

end VG.Generic.Sha256.X86.Stream

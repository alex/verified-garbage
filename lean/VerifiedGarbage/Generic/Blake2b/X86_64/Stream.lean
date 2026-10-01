import VerifiedGarbage.Proof.Blake2.X86_64.Backend

/-!
# Streaming BLAKE2b on x86-64, for every compression backend

The reviewed APIs supply signatures and contracts. Names carry the backend's
suffix, and every streaming caller calls that backend's compression function.
Initialization is backend-independent and stays in the registration file.
-/

namespace VG.Generic.Blake2b.X86_64.Stream

def artifacts (v : Proof.Blake2.X86_64.Backend) : List Artifact := [
  { Spec.Blake2.compressBApi with
    name := v.compressName
    target := VG.X86_64.target
    doc := Spec.Blake2.compressBApi.doc
    code := v.code
    contract := Spec.Blake2.compressBContract VG.X86_64.abi
    verified := v.verified
    spSafe := v.spSafe
    features := v.features },
  { Spec.Blake2.updateBApi with
    name := v.updateName
    target := VG.X86_64.target
    doc := Spec.Blake2.updateBApi.doc
    code := v.update
    contract := Spec.Blake2.updateBContract VG.X86_64.abi 8
    stack := 8
    verified := v.update_verified
    spSafe := v.updateSpSafe
    features := v.features },
  { Spec.Blake2.finalizeBApi with
    name := v.finalizeName
    target := VG.X86_64.target
    doc := Spec.Blake2.finalizeBApi.doc
    code := v.finalize
    contract := Spec.Blake2.finalizeBContract VG.X86_64.abi 8
    stack := 8
    verified := v.finalize_verified
    spSafe := v.finalizeSpSafe
    features := v.features }]

end VG.Generic.Blake2b.X86_64.Stream

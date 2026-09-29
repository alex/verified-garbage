import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha1.X86_64.Shared
import VerifiedGarbage.Proof.Sha1.X86_64.Variant

/-!
# Streaming SHA-1 (FIPS 180-4) on x86-64

A generic file (see `TCB/Emit.lean`): `update` and `finalize`, calling an
implementation `v` of the SHA-1 compression function, are emitted once for
each implementation (`Variants/Sha1Compress/X86_64/`), named with its
suffix (e.g. `vg_sha1_update_shani`). **Review note**: `sig` and `doc` are
trusted, as they tie the Rust caller to the contract; check them against the
contract's `pre`/`post`. An artifact made from a function's `Api` (in
`Spec/`, reviewed with the contract) takes them from there. The emitter adds
the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract, and the
CPU features the implementation needs.
-/

namespace VG.Generic.Sha1Compress.X86_64.Sha1

def artifacts (v : Proof.Sha1.X86_64.Compress) : List Artifact := [
  { Spec.Sha1.updateApi with
    name := Spec.Sha1.updateApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Sha1.updateApi.doc
    code := Impl.Sha1.X86_64.Stream.update v.callee
    contract := Spec.Sha1.updateContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha1.X86_64.Shared.update v.ok v.mxcsr
    spSafe := Proof.Sha1.X86_64.Shared.update_spSafe v.spSafe
    features := v.features },
  { Spec.Sha1.finalizeApi with
    name := Spec.Sha1.finalizeApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Sha1.finalizeApi.doc
    code := Impl.Sha1.X86_64.Stream.finalize v.callee
    contract := Spec.Sha1.finalizeContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha1.X86_64.Shared.finalize v.ok v.mxcsr
    spSafe := Proof.Sha1.X86_64.Shared.finalize_spSafe v.spSafe
    features := v.features }]

end VG.Generic.Sha1Compress.X86_64.Sha1

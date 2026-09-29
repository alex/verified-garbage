import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Pbkdf2.X86_64
import VerifiedGarbage.Proof.Sha256.X86_64.Variant
import VerifiedGarbage.Proof.Pbkdf2.X86_64.IterateCT

/-!
# The PBKDF2-HMAC-SHA-256 iteration (RFC 8018) on x86-64

A generic file (see `TCB/Emit.lean`): the iteration, calling an
implementation `v` of the SHA-256 compression function, is emitted once for
each implementation (`Variants/Sha256Compress/X86_64/`), named with its
suffix (e.g. `vg_pbkdf2_hmac_sha256_iterate_shani`). **Review note**: `sig`
and `doc` are trusted, as they tie the Rust caller to the contract; check
them against the contract's `pre`/`post`. An artifact made from a function's
`Api` (in `Spec/`, reviewed with the contract) takes them from there. The
emitter adds the `# Safety` items that depend on the target
(`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract, and the CPU features the implementation needs.
-/

namespace VG.Generic.Sha256Compress.X86_64.Pbkdf2

def artifacts (v : Proof.Sha256.X86_64.Compress) : List Artifact := [
  { Spec.Pbkdf2.iterateSha256Api with
    name := Spec.Pbkdf2.iterateSha256Api.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Pbkdf2.iterateSha256Api.doc
    code := Impl.Pbkdf2.X86_64.iterate v.callee
    contract := Spec.Pbkdf2.iterateSha256Contract X86_64.abi 8
    stack := 8
    verified := Proof.Pbkdf2.X86_64.Iterate.iterate_verified v.ok v.mxcsr
    spSafe := Proof.Pbkdf2.X86_64.Iterate.iterate_spSafe v.spSafe
    features := v.features }]

end VG.Generic.Sha256Compress.X86_64.Pbkdf2

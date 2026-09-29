import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Pbkdf2.X86_64
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Shared
import VerifiedGarbage.Proof.Sha256.X86_64.Variant

/-!
# PBKDF2-HMAC-SHA-256 (RFC 8018) on x86-64

A generic file (see `TCB/Emit.lean`): the iteration, calling an
implementation `v` of the SHA-256 compression function, and the whole
derivation, calling the SHA-256, HMAC-SHA-256 and iteration functions made
with the same implementation, are emitted once for each implementation
(`Variants/Sha256Compress/X86_64/`), named with its suffix (e.g.
`vg_pbkdf2_hmac_sha256_iterate_shani`, `vg_pbkdf2_hmac_sha256_shani`). **Review note**: `sig`
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
    verified := Proof.Pbkdf2.X86_64.Shared.iterate v.ok v.mxcsr
    spSafe := Proof.Pbkdf2.X86_64.Shared.iterate_spSafe v.spSafe
    features := v.features },
  { Spec.Pbkdf2.pbkdf2Sha256Api with
    name := Spec.Pbkdf2.pbkdf2Sha256Api.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Pbkdf2.pbkdf2Sha256Api.doc (notes := [
      "Each 32-byte block `T_i` starts from a copy of the key's inner HMAC state that has \
        already absorbed the salt: `vg_sha256_update` adds `INT (i)` and `vg_hmac_sha256_finalize` \
        gives `U₁`, then `vg_pbkdf2_hmac_sha256_iterate` the other `c - 1` steps, each called \
        with this function's suffix. A password longer than 64 bytes is hashed first."])
    code := Impl.Pbkdf2.X86_64.derive v.callee v.suffix
    contract := Spec.Pbkdf2.pbkdf2Sha256Contract X86_64.abi 24
    stack := 24
    verified := Proof.Pbkdf2.X86_64.Shared.derive v.ok v.mxcsr v.suffix
    spSafe := Proof.Pbkdf2.X86_64.Shared.derive_spSafe v.spSafe v.suffix
    features := v.features }]

end VG.Generic.Sha256Compress.X86_64.Pbkdf2

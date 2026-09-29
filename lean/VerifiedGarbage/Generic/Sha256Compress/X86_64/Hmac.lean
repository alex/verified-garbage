import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha256.X86_64.Variant
import VerifiedGarbage.Proof.Hmac.X86_64.Init
import VerifiedGarbage.Proof.Hmac.X86_64.Finalize

/-!
# HMAC-SHA-256 (RFC 2104) on x86-64

A generic file (see `TCB/Emit.lean`): `init` and `finalize`, calling an
implementation `v` of the SHA-256 compression function (`finalize` through
the streaming finalization made with it, which `Sha256.lean` here emits as
`vg_sha256_finalize` with `v`'s suffix), are emitted once for each
implementation (`Variants/Sha256Compress/X86_64/`), named with its suffix
(e.g. `vg_hmac_sha256_init_shani`). **Review note**: `sig` and `doc` are
trusted, as they tie the Rust caller to the contract; check them against the
contract's `pre`/`post`. An artifact made from a function's `Api` (in
`Spec/`, reviewed with the contract) takes them from there. The emitter adds
the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract, and the
CPU features the implementation needs.
-/

namespace VG.Generic.Sha256Compress.X86_64.Hmac

def artifacts (v : Proof.Sha256.X86_64.Compress) : List Artifact := [
  { Spec.Hmac.initSha256Api with
    name := Spec.Hmac.initSha256Api.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.initSha256Api.doc
    code := Impl.Hmac.X86_64.init v.callee
    contract := Spec.Hmac.initSha256Contract X86_64.abi 8
    stack := 8
    verified := Proof.Hmac.X86_64.Init.init_verified v.ok v.mxcsr
    spSafe := Proof.Hmac.X86_64.Init.init_spSafe v.spSafe
    features := v.features },
  { Spec.Hmac.finalizeSha256Api with
    name := Spec.Hmac.finalizeSha256Api.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.finalizeSha256Api.doc
    code := Impl.Hmac.X86_64.finalize v.callee (Spec.Sha256.finalizeApi.name ++ v.suffix)
    contract := Spec.Hmac.finalizeSha256Contract X86_64.abi 16
    stack := 16
    verified := Proof.Hmac.X86_64.Finalize.finalize_verified v.ok v.mxcsr _
    spSafe := Proof.Hmac.X86_64.Finalize.finalize_spSafe v.spSafe _
    features := v.features }]

end VG.Generic.Sha256Compress.X86_64.Hmac

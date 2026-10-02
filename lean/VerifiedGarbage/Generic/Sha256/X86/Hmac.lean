import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-!
# HMAC-SHA-256 (RFC 2104) on x86

A generic file (see `TCB/Emit.lean`): HMAC's `init` and `finalize`, the one
implementation for every streaming hash function
(`Impl/Hmac/Generic/X86.lean`), calling SHA-256's streaming functions made
with the variant's compression function, are emitted once for each variant
(`Variants/Sha256/X86/`), named with its suffix. **Review note**: `sig` and
`doc` are trusted, as they tie the Rust caller to the contract; check them
against the contract's `pre`/`post`. An artifact made from a function's
`Api` (in `Spec/`, reviewed with the contract) takes them from there. The
emitter adds the `# Safety` items that depend on the target
(`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks against
the contract (after unfolding the `Instance`'s contract to the generic one,
which is a `Sig.contract`), and the CPU features the implementation needs.
-/

namespace VG.Generic.Sha256.X86.Hmac

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  { Spec.Hmac.sha256I.initApi with
    name := Spec.Hmac.sha256I.initApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.initApi.doc
    code := v.H.init
    contract := Spec.Hmac.sha256I.initContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48
    verified := v.hmacInit
    spSafe := v.initSp
    features := v.features },
  { Spec.Hmac.sha256I.finalizeApi with
    name := Spec.Hmac.sha256I.finalizeApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.finalizeApi.doc
    code := v.H.finalize
    contract := Spec.Hmac.sha256I.finalizeContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48
    verified := v.hmacFin
    spSafe := v.finSp
    features := v.features }]

end VG.Generic.Sha256.X86.Hmac

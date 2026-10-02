import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-!
# The PBKDF2-HMAC-SHA-256 iteration (RFC 8018) on x86

A generic file (see `TCB/Emit.lean`): PBKDF2's `iterate`, the one iteration
for every streaming hash function (`Impl/Pbkdf2/Generic/X86.lean`), calling
SHA-256's streaming functions made with the variant's compression function,
is emitted once for each variant (`Variants/Sha256/X86/`), named with its
suffix. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there. The emitter adds the `# Safety` items that
depend on the target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which
`ofSig` checks against the contract (after unfolding the `Instance`'s
contract to the generic one, which is a `Sig.contract`), and the CPU
features the implementation needs.
-/

namespace VG.Generic.Sha256.X86.Pbkdf2

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  { Spec.Hmac.sha256I.iterateApi with
    name := Spec.Hmac.sha256I.iterateApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.X86.iterate v.H
    contract := Spec.Hmac.sha256I.iterateContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    stack := 48
    verified := v.iterate
    spSafe := v.iterSp
    features := v.features }]

end VG.Generic.Sha256.X86.Pbkdf2

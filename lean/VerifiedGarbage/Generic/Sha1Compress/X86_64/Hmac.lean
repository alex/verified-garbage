import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha1.X86_64.Variant
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Instances

/-!
# HMAC-SHA-1 (RFC 2104) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of the SHA-1 compression function (through the streaming
functions made with it, which `Sha1.lean` here emits named with its suffix),
are emitted once for each implementation (`Variants/Sha1Compress/X86_64/`),
named with its suffix (e.g. `vg_hmac_sha1_init_shani`), and need its CPU
features. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract (after unfolding the `Instance`'s contract to the
generic one, which is a `Sig.contract`).

The code is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/X86_64.lean`), calling SHA-1's verified `init`, `update`
and `finalize`.
-/

namespace VG.Generic.Sha1Compress.X86_64.Hmac

open VG.Proof.Hmac.Generic.X86_64

def artifacts (v : Proof.Sha1.X86_64.Compress) : List Artifact := [
  { Spec.Hmac.sha1I.initApi with
    name := Spec.Hmac.sha1I.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha1I.initApi.doc
    code := (sha1H v).init
    contract := Spec.Hmac.sha1I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha1_init v
    spSafe := Instances.sha1_initSp v
    features := v.features },
  { Spec.Hmac.sha1I.finalizeApi with
    name := Spec.Hmac.sha1I.finalizeApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha1I.finalizeApi.doc
    code := (sha1H v).finalize
    contract := Spec.Hmac.sha1I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha1_finalize v
    spSafe := Instances.sha1_finSp v
    features := v.features }]

end VG.Generic.Sha1Compress.X86_64.Hmac

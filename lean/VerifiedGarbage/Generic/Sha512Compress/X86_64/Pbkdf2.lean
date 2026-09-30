import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Instances

/-!
# The PBKDF2-HMAC-SHA-384, -SHA-512, -SHA-512/224 and -SHA-512/256 iterations (RFC 8018) on x86-64

A generic file (see `TCB/Emit.lean`): the iterations, calling an
implementation `v` of the SHA-512 compression function, are emitted once for
each implementation (`Variants/Sha512Compress/X86_64/`), named with its
suffix (e.g. `vg_pbkdf2_hmac_sha384_iterate_avx2`), and need its CPU
features. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract (after unfolding the `Instance`'s contract to the
generic one, which is a `Sig.contract`).

The code is the one PBKDF2 iteration for every hash function whose streaming
code is the generic one (`Impl/Pbkdf2/X86_64.lean`), calling the verified
compression function `v` directly, twice per step.
-/

namespace VG.Generic.Sha512Compress.X86_64.Pbkdf2

def artifacts (v : Proof.Sha512.X86_64.Compress) : List Artifact := [
  { Spec.Hmac.sha384I.iterateApi with
    name := Spec.Hmac.sha384I.iterateApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha384I.iterateApi.doc
    code := Proof.Pbkdf2.X86_64.Instances.sha384Iterate v
    contract := Spec.Hmac.sha384I.iterateContract X86_64.abi 8
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 8
    verified := Proof.Pbkdf2.X86_64.Instances.sha384 v
    spSafe := Proof.Pbkdf2.X86_64.Instances.sha384_sp v
    features := v.features },
  { Spec.Hmac.sha512I.iterateApi with
    name := Spec.Hmac.sha512I.iterateApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha512I.iterateApi.doc
    code := Proof.Pbkdf2.X86_64.Instances.sha512Iterate v
    contract := Spec.Hmac.sha512I.iterateContract X86_64.abi 8
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 8
    verified := Proof.Pbkdf2.X86_64.Instances.sha512 v
    spSafe := Proof.Pbkdf2.X86_64.Instances.sha512_sp v
    features := v.features },
  { Spec.Hmac.sha512_224I.iterateApi with
    name := Spec.Hmac.sha512_224I.iterateApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha512_224I.iterateApi.doc
    code := Proof.Pbkdf2.X86_64.Instances.sha512_224Iterate v
    contract := Spec.Hmac.sha512_224I.iterateContract X86_64.abi 8
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 8
    verified := Proof.Pbkdf2.X86_64.Instances.sha512_224 v
    spSafe := Proof.Pbkdf2.X86_64.Instances.sha512_224_sp v
    features := v.features },
  { Spec.Hmac.sha512_256I.iterateApi with
    name := Spec.Hmac.sha512_256I.iterateApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Hmac.sha512_256I.iterateApi.doc
    code := Proof.Pbkdf2.X86_64.Instances.sha512_256Iterate v
    contract := Spec.Hmac.sha512_256I.iterateContract X86_64.abi 8
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 8
    verified := Proof.Pbkdf2.X86_64.Instances.sha512_256 v
    spSafe := Proof.Pbkdf2.X86_64.Instances.sha512_256_sp v
    features := v.features }]

end VG.Generic.Sha512Compress.X86_64.Pbkdf2

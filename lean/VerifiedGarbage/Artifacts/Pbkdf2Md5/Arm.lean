import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances

/-!
# PBKDF2-HMAC-MD5 (RFC 8018) on ARMv7: the iteration and the whole derivation

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract (after unfolding the `Instance`'s contract to the
generic one, which is a `Sig.contract`).

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`): each step is two calls of MD5's verified
compression function (`vg_md5_compress`), on blocks laid out once at fixed
offsets in `scratch`. It uses no stack; `stack` is that of the shared
contract, 16 bytes.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/Arm.lean`), calling the hash function's streaming
functions, HMAC's `init` and `finalize` and the iteration above. `stack` is
that of the shared contract, 24 bytes: `pbkdf2` pushes `update`'s 16 bytes of
stack arguments, or 8 bytes around a call of a function that uses 16.
-/

namespace VG.Artifacts.Pbkdf2Md5.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.md5I.iterateApi with
    target := Arm.target
    doc := Spec.Hmac.md5I.iterateApi.doc
    code := Proof.Pbkdf2.Md.Arm.md5Md.iterate
    contract := Spec.Hmac.md5I.iterateContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.md5_iterate
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.md5I.pbkdf2Api with
    target := Arm.target
    doc := Spec.Hmac.md5I.pbkdf2Api.doc
    code := Proof.Pbkdf2.Whole.Arm.md5F.pbkdf2
    contract := Spec.Hmac.md5I.pbkdf2Contract Arm.abi 24
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract; rfl⟩
    stack := 24
    verified := Proof.Pbkdf2.Whole.Arm.md5
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Pbkdf2Md5.Arm

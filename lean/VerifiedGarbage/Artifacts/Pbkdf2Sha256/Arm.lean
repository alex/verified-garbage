import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Pbkdf2.Arm
import VerifiedGarbage.Proof.Pbkdf2.Arm.Iterate
import VerifiedGarbage.Proof.Pbkdf2.Arm.Lit
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256

/-!
# PBKDF2-HMAC-SHA-256 (RFC 8018) on 32-bit ARM: the iteration and the whole derivation

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/Arm.lean`), calling SHA-256's streaming functions,
HMAC-SHA-256's `init` and `finalize` and the iteration above, which use no
stack. Its `stack` is that of the shared contract: 24 bytes (it pushes up to
16).
-/

namespace VG.Artifacts.Pbkdf2Sha256.Arm

def artifacts : List Artifact := [
  { Spec.Pbkdf2.iterateSha256Api with
    target := Arm.target
    doc := Spec.Pbkdf2.iterateSha256Api.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Pbkdf2.Arm.iterate
    contract := Spec.Pbkdf2.iterateSha256Contract Arm.abi
    verified := Proof.Pbkdf2.Arm.iterate_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha256I.pbkdf2Api with
    target := Arm.target
    doc := Spec.Hmac.sha256I.pbkdf2Api.doc
    code := Proof.Pbkdf2.Whole.Arm.sha256F.pbkdf2
    contract := Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract; rfl⟩
    stack := 24
    verified := Proof.Pbkdf2.Whole.Arm.sha256
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Pbkdf2Sha256.Arm

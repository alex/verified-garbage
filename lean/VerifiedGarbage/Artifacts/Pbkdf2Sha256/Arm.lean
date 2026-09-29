import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Pbkdf2.Arm
import VerifiedGarbage.Proof.Pbkdf2.Arm.Iterate
import VerifiedGarbage.Proof.Pbkdf2.Arm.Lit

/-!
# The PBKDF2-HMAC-SHA-256 iteration (RFC 8018) on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
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
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Pbkdf2Sha256.Arm

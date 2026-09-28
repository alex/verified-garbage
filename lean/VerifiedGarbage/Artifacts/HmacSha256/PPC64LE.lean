import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Hmac.PPC64LE.Shared

/-!
# HMAC-SHA-256 (RFC 2104) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.HmacSha256.PPC64LE

def artifacts : List Artifact := [
  { Spec.Hmac.sha256I.initApi with
    target := PPC64LE.target
    doc := Spec.Hmac.sha256I.initApi.doc
    code := Impl.Hmac.PPC64LE.init
    contract := Spec.Hmac.sha256I.initContract PPC64LE.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 48
    verified := Proof.Hmac.PPC64LE.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha256I.finalizeApi with
    target := PPC64LE.target
    doc := Spec.Hmac.sha256I.finalizeApi.doc
    code := Impl.Hmac.PPC64LE.finalize
    contract := Spec.Hmac.sha256I.finalizeContract PPC64LE.abi 96
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 96
    verified := Proof.Hmac.PPC64LE.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha256.PPC64LE

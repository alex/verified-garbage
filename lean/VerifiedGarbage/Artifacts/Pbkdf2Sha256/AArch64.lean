import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Pbkdf2.AArch64
import VerifiedGarbage.Impl.Pbkdf2.AArch64.Derive
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Shared

/-!
# PBKDF2-HMAC-SHA-256 (RFC 8018) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Pbkdf2Sha256.AArch64

def artifacts : List Artifact := [
  { Spec.Pbkdf2.iterateSha256Api with
    target := AArch64.target
    doc := Spec.Pbkdf2.iterateSha256Api.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Pbkdf2.AArch64.iterate
    contract := Spec.Pbkdf2.iterateSha256Contract AArch64.abi
    verified := Proof.Pbkdf2.AArch64.Shared.iterate
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Pbkdf2.pbkdf2Sha256Api with
    target := AArch64.target
    doc := Spec.Pbkdf2.pbkdf2Sha256Api.doc (notes := [
      "Each 32-byte block `T_i` starts from a copy of the key's inner HMAC state that has \
        already absorbed the salt: `vg_sha256_update` adds `INT (i)` and `vg_hmac_sha256_finalize` \
        gives `U₁`, then `vg_pbkdf2_hmac_sha256_iterate` the other `c - 1` steps. A password \
        longer than 64 bytes is hashed first.",
      "The function saves its return address in a 16-byte stack frame, and the caller's `x19` to \
        `x26` in `scratch`."])
    code := Impl.Pbkdf2.AArch64.derive
    contract := Spec.Pbkdf2.pbkdf2Sha256Contract AArch64.abi 48
    stack := 48
    verified := Proof.Pbkdf2.AArch64.Shared.derive
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Pbkdf2Sha256.AArch64

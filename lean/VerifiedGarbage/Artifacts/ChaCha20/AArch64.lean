import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Init

/-!
# The ChaCha20 block function (RFC 8439) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.ChaCha20.AArch64

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := AArch64.target
    doc := Spec.ChaCha20.blockApi.doc
    code := Impl.ChaCha20.AArch64.block
    contract := Spec.ChaCha20.blockContract AArch64.abi
    verified := Proof.ChaCha20.AArch64.block_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.initApi with
    target := AArch64.target
    doc := Spec.ChaCha20.initApi.doc
    code := Impl.ChaCha20.AArch64.Stream.init
    contract := Spec.ChaCha20.initContract AArch64.abi
    verified := Proof.ChaCha20.AArch64.Stream.init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.setNonceApi with
    target := AArch64.target
    doc := Spec.ChaCha20.setNonceApi.doc
    code := Impl.ChaCha20.AArch64.Stream.setNonce
    contract := Spec.ChaCha20.setNonceContract AArch64.abi
    verified := Proof.ChaCha20.AArch64.Stream.setNonce_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20.AArch64

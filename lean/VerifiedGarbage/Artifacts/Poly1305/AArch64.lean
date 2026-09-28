import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Poly1305.AArch64
import VerifiedGarbage.Proof.Poly1305.AArch64.Shared

/-!
# Poly1305 (RFC 8439 §2.5) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Poly1305.AArch64

def artifacts : List Artifact := [
  { Spec.Poly1305.initApi with
    target := AArch64.target
    doc := Spec.Poly1305.initApi.doc
    code := Impl.Poly1305.AArch64.init
    contract := Spec.Poly1305.initContract AArch64.abi
    verified := Proof.Poly1305.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Poly1305.blocksApi with
    target := AArch64.target
    doc := Spec.Poly1305.blocksApi.doc
    code := Impl.Poly1305.AArch64.blocks
    contract := Spec.Poly1305.blocksContract AArch64.abi
    verified := Proof.Poly1305.AArch64.Shared.blocks
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Poly1305.finalizeTailApi with
    target := AArch64.target
    doc := Spec.Poly1305.finalizeTailApi.doc
    code := Impl.Poly1305.AArch64.finalize
    contract := Spec.Poly1305.finalizeTailContract AArch64.abi
    verified := Proof.Poly1305.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Poly1305.AArch64

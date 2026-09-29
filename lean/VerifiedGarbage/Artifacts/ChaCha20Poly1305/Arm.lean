import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Shared

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract. The functions use 8 bytes of stack: they push the two
stack arguments of `vg_poly1305_finalize` around its call; their calls
(`bl`) keep the return address in `lr`, which they save in the context.
-/

namespace VG.Artifacts.ChaCha20Poly1305.Arm

def artifacts : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    target := Arm.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc
    code := Impl.ChaCha20Poly1305.Arm.«seal»
    contract := Spec.ChaCha20Poly1305.sealContract Arm.abi 8
    stack := 8
    verified := Proof.ChaCha20Poly1305.Arm.Shared.«seal»
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20Poly1305.openApi with
    target := Arm.target
    doc := Spec.ChaCha20Poly1305.openApi.doc
    code := Impl.ChaCha20Poly1305.Arm.«open»
    contract := Spec.ChaCha20Poly1305.openContract Arm.abi 8
    stack := 8
    verified := Proof.ChaCha20Poly1305.Arm.Shared.«open»
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20Poly1305.Arm

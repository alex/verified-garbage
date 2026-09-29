import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Shared
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Xor

/-!
# The ChaCha20 block function (RFC 8439) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.ChaCha20.PPC64LE

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := PPC64LE.target
    doc := Spec.ChaCha20.blockApi.doc
    code := Impl.ChaCha20.PPC64LE.block
    contract := Spec.ChaCha20.blockContract PPC64LE.abi
    verified := Proof.ChaCha20.PPC64LE.Shared.block
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.xorApi with
    target := PPC64LE.target
    doc := Spec.ChaCha20.xorApi.doc
    code := Impl.ChaCha20.PPC64LE.Xor.xor
    contract := Spec.ChaCha20.xorContract PPC64LE.abi
    verified := Proof.ChaCha20.PPC64LE.Xor.xor_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20.PPC64LE

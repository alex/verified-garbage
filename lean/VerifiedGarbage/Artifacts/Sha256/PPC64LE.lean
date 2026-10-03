import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Sha256.PPC64LE.Shared

/-!
# SHA-256 (FIPS 180-4) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha256.PPC64LE

def artifacts : List Artifact := [
  { Spec.Sha256.compressApi with
    target := PPC64LE.target
    doc := Spec.Sha256.compressApi.doc
    code := Impl.Sha256.PPC64LE.compress
    contract := Spec.Sha256.compressContract PPC64LE.abi
    verified := Proof.Sha256.PPC64LE.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha256.initApi with
    target := PPC64LE.target
    doc := Spec.Sha256.initApi.doc
    code := Impl.Sha256.PPC64LE.Stream.init
    contract := Spec.Sha256.initContract PPC64LE.abi
    verified := Proof.Sha256.PPC64LE.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha256.updateApi with
    target := PPC64LE.target
    doc := Spec.Sha256.updateApi.doc
    code := Impl.Sha256.PPC64LE.Stream.update
    contract := Spec.Sha256.updateContract PPC64LE.abi 48
    stack := 48
    verified := Proof.Sha256.PPC64LE.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha256.finalizeApi with
    target := PPC64LE.target
    doc := Spec.Sha256.finalizeApi.doc
    code := Impl.Sha256.PPC64LE.Stream.finalize
    contract := Spec.Sha256.finalizeContract PPC64LE.abi 48
    stack := 48
    verified := Proof.Sha256.PPC64LE.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha256.PPC64LE

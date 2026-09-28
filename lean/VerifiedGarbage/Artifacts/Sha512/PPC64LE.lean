import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Sha512.PPC64LE.Shared

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha512.PPC64LE

def artifacts : List Artifact := [
  { Spec.Sha512.compressApi with
    target := PPC64LE.target
    doc := Spec.Sha512.compressApi.doc
    code := Impl.Sha512.PPC64LE.compress
    contract := Spec.Sha512.compressContract PPC64LE.abi
    verified := Proof.Sha512.PPC64LE.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init384Api with
    target := PPC64LE.target
    doc := Spec.Sha512.init384Api.doc
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract PPC64LE.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_384
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512Api with
    target := PPC64LE.target
    doc := Spec.Sha512.init512Api.doc
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract PPC64LE.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_512
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512_224Api with
    target := PPC64LE.target
    doc := Spec.Sha512.init512_224Api.doc
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract PPC64LE.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_512_224
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512_256Api with
    target := PPC64LE.target
    doc := Spec.Sha512.init512_256Api.doc
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract PPC64LE.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_512_256
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.updateApi with
    target := PPC64LE.target
    doc := Spec.Sha512.updateApi.doc
    code := Impl.Sha512.PPC64LE.Stream.update
    contract := Spec.Sha512.updateContract PPC64LE.abi
    verified := Proof.Sha512.PPC64LE.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.finalizeApi with
    target := PPC64LE.target
    doc := Spec.Sha512.finalizeApi.doc
    code := Impl.Sha512.PPC64LE.Stream.finalize
    contract := Spec.Sha512.finalizeContract PPC64LE.abi
    verified := Proof.Sha512.PPC64LE.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha512.PPC64LE

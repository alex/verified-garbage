import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha512.AArch64.Shared

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha512.AArch64

def artifacts : List Artifact := [
  { Spec.Sha512.compressApi with
    target := AArch64.target
    doc := Spec.Sha512.compressApi.doc
    code := Impl.Sha512.AArch64.compress
    contract := Spec.Sha512.compressContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init384Api with
    target := AArch64.target
    doc := Spec.Sha512.init384Api.doc
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_384
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512Api with
    target := AArch64.target
    doc := Spec.Sha512.init512Api.doc
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512_224Api with
    target := AArch64.target
    doc := Spec.Sha512.init512_224Api.doc
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512_224
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512_256Api with
    target := AArch64.target
    doc := Spec.Sha512.init512_256Api.doc
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512_256
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.updateApi with
    target := AArch64.target
    doc := Spec.Sha512.updateApi.doc
    code := Impl.Sha512.AArch64.Stream.update
    contract := Spec.Sha512.updateContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.finalizeApi with
    target := AArch64.target
    doc := Spec.Sha512.finalizeApi.doc
    code := Impl.Sha512.AArch64.Stream.finalize
    contract := Spec.Sha512.finalizeContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha512.AArch64

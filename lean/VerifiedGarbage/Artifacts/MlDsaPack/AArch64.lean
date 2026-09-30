import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack

/-!
# ML-DSA (FIPS 204) on AArch64: the encodings

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaPack.AArch64

def artifacts : List Artifact := [
  { Spec.MlDsa.simpleBitPackApi with
    target := AArch64.target
    doc := Spec.MlDsa.simpleBitPackApi.doc
    code := Impl.MlDsa.AArch64.Pack.simpleBitPack
    contract := Spec.MlDsa.simpleBitPackContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Pack.simpleBitPack_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.bitPackApi with
    target := AArch64.target
    doc := Spec.MlDsa.bitPackApi.doc
    code := Impl.MlDsa.AArch64.Pack.bitPack
    contract := Spec.MlDsa.bitPackContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Pack.bitPack_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.bitUnpackApi with
    target := AArch64.target
    doc := Spec.MlDsa.bitUnpackApi.doc
    code := Impl.MlDsa.AArch64.Pack.bitUnpack
    contract := Spec.MlDsa.bitUnpackContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Pack.bitUnpack_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.unpackT1Api with
    target := AArch64.target
    doc := Spec.MlDsa.unpackT1Api.doc
    code := Impl.MlDsa.AArch64.Pack.unpackT1
    contract := Spec.MlDsa.unpackT1Contract AArch64.abi
    verified := Proof.MlDsa.AArch64.Pack.unpackT1_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.hintBitPackApi with
    target := AArch64.target
    doc := Spec.MlDsa.hintBitPackApi.doc
    code := Impl.MlDsa.AArch64.Pack.hintBitPack
    contract := Spec.MlDsa.hintBitPackContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Pack.hintBitPack_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.hintBitUnpackApi with
    target := AArch64.target
    doc := Spec.MlDsa.hintBitUnpackApi.doc
    code := Impl.MlDsa.AArch64.Pack.hintBitUnpack
    contract := Spec.MlDsa.hintBitUnpackContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Pack.hintBitUnpack_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaPack.AArch64

import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlKem.AArch64.AddSub
import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
import VerifiedGarbage.Proof.MlKem.AArch64.Mul
import VerifiedGarbage.Proof.MlKem.AArch64.NttInv

/-!
# ML-KEM on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlKem.AArch64

def artifacts : List Artifact := [
  { Spec.MlKem.addApi with
    target := AArch64.target
    doc := Spec.MlKem.addApi.doc
    code := Impl.MlKem.AArch64.add
    contract := Spec.MlKem.addContract AArch64.abi
    verified := Proof.MlKem.AArch64.add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.subApi with
    target := AArch64.target
    doc := Spec.MlKem.subApi.doc
    code := Impl.MlKem.AArch64.sub
    contract := Spec.MlKem.subContract AArch64.abi
    verified := Proof.MlKem.AArch64.sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.encode12Api with
    target := AArch64.target
    doc := Spec.MlKem.encode12Api.doc
    code := Impl.MlKem.AArch64.encode12
    contract := Spec.MlKem.encode12Contract AArch64.abi
    verified := Proof.MlKem.AArch64.Encode12.encode12_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.decode12Api with
    target := AArch64.target
    doc := Spec.MlKem.decode12Api.doc
    code := Impl.MlKem.AArch64.decode12
    contract := Spec.MlKem.decode12Contract AArch64.abi
    verified := Proof.MlKem.AArch64.Decode12.decode12_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.cbd2Api with
    target := AArch64.target
    doc := Spec.MlKem.cbd2Api.doc
    code := Impl.MlKem.AArch64.cbd2
    contract := Spec.MlKem.cbd2Contract AArch64.abi
    verified := Proof.MlKem.AArch64.Cbd2.cbd2_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.compressEncodeApi with
    target := AArch64.target
    doc := Spec.MlKem.compressEncodeApi.doc
    code := Impl.MlKem.AArch64.compressEncode
    contract := Spec.MlKem.compressEncodeContract AArch64.abi
    verified := Proof.MlKem.AArch64.CE.compressEncode_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.decodeDecompressApi with
    target := AArch64.target
    doc := Spec.MlKem.decodeDecompressApi.doc
    code := Impl.MlKem.AArch64.decodeDecompress
    contract := Spec.MlKem.decodeDecompressContract AArch64.abi
    verified := Proof.MlKem.AArch64.DD.decodeDecompress_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.checkEkApi with
    target := AArch64.target
    doc := Spec.MlKem.checkEkApi.doc
    code := Impl.MlKem.AArch64.checkEk
    contract := Spec.MlKem.checkEkContract AArch64.abi
    verified := Proof.MlKem.AArch64.CheckEk.checkEk_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.mulApi with
    target := AArch64.target
    doc := Spec.MlKem.mulApi.doc
    code := Impl.MlKem.AArch64.multiplyNTTs
    contract := Spec.MlKem.mulContract AArch64.abi
    verified := Proof.MlKem.AArch64.Mul.mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.nttApi with
    target := AArch64.target
    doc := Spec.MlKem.nttApi.doc
    code := Impl.MlKem.AArch64.ntt
    contract := Spec.MlKem.nttContract AArch64.abi
    verified := Proof.MlKem.AArch64.Ntt.ntt_verified
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttContract Spec.MlKem.inPlaceContract; rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.nttInvApi with
    target := AArch64.target
    doc := Spec.MlKem.nttInvApi.doc
    code := Impl.MlKem.AArch64.nttInv
    contract := Spec.MlKem.nttInvContract AArch64.abi
    verified := Proof.MlKem.AArch64.Ntt.ntt_inv_verified
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttInvContract Spec.MlKem.inPlaceContract; rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlKem.AArch64

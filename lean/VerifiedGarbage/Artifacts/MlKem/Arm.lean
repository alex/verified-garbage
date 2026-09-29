import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlKem.Arm.Encode12
import VerifiedGarbage.Proof.MlKem.Arm.Decode12
import VerifiedGarbage.Proof.MlKem.Arm.Cbd2
import VerifiedGarbage.Proof.MlKem.Arm.CheckEk
import VerifiedGarbage.Proof.MlKem.Arm.CompressEncode
import VerifiedGarbage.Proof.MlKem.Arm.Decompress
import VerifiedGarbage.Proof.MlKem.Arm.Mul
import VerifiedGarbage.Proof.MlKem.Arm.NttInv
import VerifiedGarbage.Proof.MlKem.Arm.SampleCT

/-!
# ML-KEM (FIPS 203) on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlKem.Arm

def artifacts : List Artifact := [
  { Spec.MlKem.sampleNTTApi with
    target := Arm.target
    doc := Spec.MlKem.sampleNTTApi.doc
      (notes := ["The function saves `r4`–`r11` and its return address in `scratch`; the 8 bytes of stack \
        below the stack pointer hold the stack arguments of the SHA-3 functions it calls."])
    code := Impl.MlKem.Arm.sampleNTT
    contract := Spec.MlKem.sampleNTTContract Arm.abi 8
    stack := 8
    verified := Proof.MlKem.Arm.Sample.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.nttApi with
    target := Arm.target
    doc := Spec.MlKem.nttApi.doc
      (notes := ["The function uses no stack: it saves `r4`–`r11` in `scratch`."])
    code := Impl.MlKem.Arm.ntt
    contract := Spec.MlKem.nttContract Arm.abi
    verified := Proof.MlKem.Arm.Ntt.verified
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttContract Spec.MlKem.inPlaceContract; exact rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.nttInvApi with
    target := Arm.target
    doc := Spec.MlKem.nttInvApi.doc
      (notes := ["The function uses no stack: it saves `r4`–`r11` in `scratch`."])
    code := Impl.MlKem.Arm.nttInv
    contract := Spec.MlKem.nttInvContract Arm.abi
    verified := Proof.MlKem.Arm.NttInv.verified
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttInvContract Spec.MlKem.inPlaceContract; exact rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.mulApi with
    target := Arm.target
    doc := Spec.MlKem.mulApi.doc
      (notes := ["The function uses no stack: it saves `r4`–`r11` in `scratch`."])
    code := Impl.MlKem.Arm.multiplyNTTs
    contract := Spec.MlKem.mulContract Arm.abi
    verified := Proof.MlKem.Arm.Mul.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.addApi with
    target := Arm.target
    doc := Spec.MlKem.addApi.doc
    code := Impl.MlKem.Arm.add
    contract := Spec.MlKem.addContract Arm.abi
    verified := Proof.MlKem.Arm.Add.add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.subApi with
    target := Arm.target
    doc := Spec.MlKem.subApi.doc
    code := Impl.MlKem.Arm.sub
    contract := Spec.MlKem.subContract Arm.abi
    verified := Proof.MlKem.Arm.Add.sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.cbd2Api with
    target := Arm.target
    doc := Spec.MlKem.cbd2Api.doc
    code := Impl.MlKem.Arm.cbd2
    contract := Spec.MlKem.cbd2Contract Arm.abi
    verified := Proof.MlKem.Arm.Cbd2.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.encode12Api with
    target := Arm.target
    doc := Spec.MlKem.encode12Api.doc
    code := Impl.MlKem.Arm.encode12
    contract := Spec.MlKem.encode12Contract Arm.abi
    verified := Proof.MlKem.Arm.Encode12.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.decode12Api with
    target := Arm.target
    doc := Spec.MlKem.decode12Api.doc
    code := Impl.MlKem.Arm.decode12
    contract := Spec.MlKem.decode12Contract Arm.abi
    verified := Proof.MlKem.Arm.Decode12.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.compressEncodeApi with
    target := Arm.target
    doc := Spec.MlKem.compressEncodeApi.doc
    code := Impl.MlKem.Arm.compressEncode
    contract := Spec.MlKem.compressEncodeContract Arm.abi
    verified := Proof.MlKem.Arm.CompressEncode.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.decodeDecompressApi with
    target := Arm.target
    doc := Spec.MlKem.decodeDecompressApi.doc
    code := Impl.MlKem.Arm.decodeDecompress
    contract := Spec.MlKem.decodeDecompressContract Arm.abi
    verified := Proof.MlKem.Arm.Decompress.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.checkEkApi with
    target := Arm.target
    doc := Spec.MlKem.checkEkApi.doc
    code := Impl.MlKem.Arm.checkEk
    contract := Spec.MlKem.checkEkContract Arm.abi
    verified := Proof.MlKem.Arm.CheckEk.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlKem.Arm

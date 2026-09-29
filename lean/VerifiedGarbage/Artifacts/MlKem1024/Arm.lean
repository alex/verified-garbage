import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlKem1024.Arm.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.Arm.Decompress
import VerifiedGarbage.Proof.MlKem1024.Arm.CheckEk
import VerifiedGarbage.Proof.MlKem1024.Arm.KeyGenCT
import VerifiedGarbage.Proof.MlKem1024.Arm.EncapsCT

/-!
# ML-KEM-1024 (FIPS 203) on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlKem1024.Arm

def artifacts : List Artifact := [
  { Spec.MlKem1024.compressEncodeApi with
    target := Arm.target
    doc := Spec.MlKem1024.compressEncodeApi.doc
    code := Impl.MlKem1024.Arm.compressEncode1024
    contract := Spec.MlKem1024.compressEncodeContract Arm.abi
    verified := Proof.MlKem1024.Arm.CompressEncode.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.decodeDecompressApi with
    target := Arm.target
    doc := Spec.MlKem1024.decodeDecompressApi.doc
    code := Impl.MlKem1024.Arm.decodeDecompress1024
    contract := Spec.MlKem1024.decodeDecompressContract Arm.abi
    verified := Proof.MlKem1024.Arm.Decompress.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.checkEkApi with
    target := Arm.target
    doc := Spec.MlKem1024.checkEkApi.doc
    code := Impl.MlKem1024.Arm.checkEk1024
    contract := Spec.MlKem1024.checkEkContract Arm.abi
    verified := Proof.MlKem1024.Arm.CheckEk.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.keyGenApi with
    target := Arm.target
    doc := Spec.MlKem1024.keyGenApi.doc
      (notes := ["The function saves `r4`–`r11` and its return address in `scratch`; the 8 bytes of stack \
        below the stack pointer hold the stack arguments of the SHA-3 functions it calls."])
    code := Impl.MlKem1024.Arm.keygen1024
    contract := Spec.MlKem1024.keyGenContract Arm.abi 8
    stack := 8
    verified := Proof.MlKem1024.Arm.KeyGen.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.encapsApi with
    target := Arm.target
    doc := Spec.MlKem1024.encapsApi.doc
      (notes := ["The function saves `r4`–`r11` and its return address in `scratch`, and copies `m` into it; \
        the 8 bytes of stack below the stack pointer hold the stack arguments of the SHA-3 functions it calls."])
    code := Impl.MlKem1024.Arm.encaps1024
    contract := Spec.MlKem1024.encapsContract Arm.abi 8
    stack := 8
    verified := Proof.MlKem1024.Arm.Encaps.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlKem1024.Arm

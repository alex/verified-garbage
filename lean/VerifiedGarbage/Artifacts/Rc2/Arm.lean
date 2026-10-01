import VerifiedGarbage.Proof.Rc2.Arm.Block
import VerifiedGarbage.Proof.Rc2.Arm.Key
import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Verified

/-! # RC2 artifacts on baseline ARMv7 -/

namespace VG.Artifacts.Rc2.Arm

def artifacts : List Artifact := [
  { Spec.Rc2.cbcEncryptApi with
    target := Arm.target
    doc := Spec.Rc2.cbcEncryptApi.doc
      (notes := ["Baseline ARMv7, calling the verified RC2 block primitive."])
    code := Impl.Rc2.Arm.Cbc.encrypt
    contract := Spec.Rc2.cbcEncryptContract Arm.abi 0
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcEncryptContract Spec.Rc2.cbcContract; rfl⟩
    verified := Proof.Rc2.Arm.Cbc.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.cbcDecryptApi with
    target := Arm.target
    doc := Spec.Rc2.cbcDecryptApi.doc
      (notes := ["Baseline ARMv7, preserving the input ciphertext for the next IV."])
    code := Impl.Rc2.Arm.Cbc.decrypt
    contract := Spec.Rc2.cbcDecryptContract Arm.abi 0
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcDecryptContract Spec.Rc2.cbcContract; rfl⟩
    verified := Proof.Rc2.Arm.Cbc.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.expandKeyApi with
    target := Arm.target
    doc := Spec.Rc2.expandKeyApi.doc
      (notes := ["Baseline ARMv7. PITABLE selection scans all 256 candidates in a fixed order."])
    code := Impl.Rc2.Arm.expandKey
    contract := Spec.Rc2.expandKeyContract Arm.abi
    stack := 0
    verified := Proof.Rc2.Arm.key_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.encryptBlockApi with
    target := Arm.target
    doc := Spec.Rc2.encryptBlockApi.doc
      (notes := ["Baseline ARMv7. Mashing scans all 64 schedule words in a fixed order."])
    code := Impl.Rc2.Arm.encryptBlock
    contract := Spec.Rc2.encryptBlockContract Arm.abi
    stack := 0
    verified := Proof.Rc2.Arm.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.decryptBlockApi with
    target := Arm.target
    doc := Spec.Rc2.decryptBlockApi.doc
      (notes := ["Baseline ARMv7. Reverse mashing scans all 64 schedule words in a fixed order."])
    code := Impl.Rc2.Arm.decryptBlock
    contract := Spec.Rc2.decryptBlockContract Arm.abi
    stack := 0
    verified := Proof.Rc2.Arm.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Rc2.Arm

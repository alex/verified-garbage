import VerifiedGarbage.Proof.Rc2.AArch64.Block
import VerifiedGarbage.Proof.Rc2.AArch64.Key
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified

/-! # RC2 artifacts on baseline AArch64 -/

namespace VG.Artifacts.Rc2.AArch64

def artifacts : List Artifact := [
  { Spec.Rc2.cbcEncryptApi with
    target := AArch64.target
    doc := Spec.Rc2.cbcEncryptApi.doc
      (notes := ["Baseline AArch64, calling the verified RC2 block primitive."])
    code := Impl.Rc2.AArch64.Cbc.encrypt
    contract := Spec.Rc2.cbcEncryptContract AArch64.abi 0
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcEncryptContract Spec.Rc2.cbcContract; rfl⟩
    verified := Proof.Rc2.AArch64.Cbc.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.cbcDecryptApi with
    target := AArch64.target
    doc := Spec.Rc2.cbcDecryptApi.doc
      (notes := ["Baseline AArch64, preserving the input ciphertext for the next IV."])
    code := Impl.Rc2.AArch64.Cbc.decrypt
    contract := Spec.Rc2.cbcDecryptContract AArch64.abi 0
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcDecryptContract Spec.Rc2.cbcContract; rfl⟩
    verified := Proof.Rc2.AArch64.Cbc.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.expandKeyApi with
    target := AArch64.target
    doc := Spec.Rc2.expandKeyApi.doc
      (notes := ["Baseline AArch64. PITABLE selection scans all 256 candidates in a fixed order."])
    code := Impl.Rc2.AArch64.expandKey
    contract := Spec.Rc2.expandKeyContract AArch64.abi
    stack := 0
    verified := Proof.Rc2.AArch64.key_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.encryptBlockApi with
    target := AArch64.target
    doc := Spec.Rc2.encryptBlockApi.doc
      (notes := ["Baseline AArch64. Mashing scans all 64 schedule words in a fixed order."])
    code := Impl.Rc2.AArch64.encryptBlock
    contract := Spec.Rc2.encryptBlockContract AArch64.abi
    stack := 0
    verified := Proof.Rc2.AArch64.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.decryptBlockApi with
    target := AArch64.target
    doc := Spec.Rc2.decryptBlockApi.doc
      (notes := ["Baseline AArch64. Reverse mashing scans all 64 schedule words in a fixed order."])
    code := Impl.Rc2.AArch64.decryptBlock
    contract := Spec.Rc2.decryptBlockContract AArch64.abi
    stack := 0
    verified := Proof.Rc2.AArch64.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Rc2.AArch64

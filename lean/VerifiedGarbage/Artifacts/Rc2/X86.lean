import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.X86.Block
import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Verified

/-! # RC2 artifacts on baseline x86 -/

namespace VG.Artifacts.Rc2.X86

def artifacts : List Artifact := [
  { Spec.Rc2.cbcEncryptApi with
    target := X86.target
    doc := Spec.Rc2.cbcEncryptApi.doc
      (notes := ["Baseline x86, calling the verified RC2 block primitive."])
    code := Impl.Rc2.X86.Cbc.encrypt
    contract := Spec.Rc2.cbcEncryptContract X86.abi 16
    stack := 16
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcEncryptContract Spec.Rc2.cbcContract; rfl⟩
    verified := Proof.Rc2.X86.Cbc.encrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Rc2.cbcDecryptApi with
    target := X86.target
    doc := Spec.Rc2.cbcDecryptApi.doc
      (notes := ["Baseline x86, preserving the input ciphertext for the next IV."])
    code := Impl.Rc2.X86.Cbc.decrypt
    contract := Spec.Rc2.cbcDecryptContract X86.abi 16
    stack := 16
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcDecryptContract Spec.Rc2.cbcContract; rfl⟩
    verified := Proof.Rc2.X86.Cbc.decrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Rc2.expandKeyApi with
    target := X86.target
    doc := Spec.Rc2.expandKeyApi.doc
      (notes := ["Baseline x86. PITABLE selection scans all 256 candidates in a fixed order."])
    code := Impl.Rc2.X86.expandKey
    contract := Spec.Rc2.expandKeyContract X86.abi
    stack := 0
    verified := Proof.Rc2.X86.key_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Rc2.encryptBlockApi with
    target := X86.target
    doc := Spec.Rc2.encryptBlockApi.doc
      (notes := ["Baseline x86. Mashing scans all 64 schedule words in a fixed order."])
    code := Impl.Rc2.X86.encryptBlock
    contract := Spec.Rc2.encryptBlockContract X86.abi
    stack := 0
    verified := Proof.Rc2.X86.encrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Rc2.decryptBlockApi with
    target := X86.target
    doc := Spec.Rc2.decryptBlockApi.doc
      (notes := ["Baseline x86. Reverse mashing scans all 64 schedule words in a fixed order."])
    code := Impl.Rc2.X86.decryptBlock
    contract := Spec.Rc2.decryptBlockContract X86.abi
    stack := 0
    verified := Proof.Rc2.X86.decrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Rc2.X86

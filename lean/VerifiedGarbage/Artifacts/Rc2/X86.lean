import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.X86.Block
import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit
import VerifiedGarbage.Proof.Rc2.X86.Stream.Verified

/-! # RC2 artifacts on baseline x86 -/

namespace VG.Artifacts.Rc2.X86

def artifacts : List Artifact := [
  { Spec.Rc2.cbcInitApi with
    target := X86.target
    doc := Spec.Rc2.cbcInitApi.doc (notes := ["Baseline x86: copies the IV and calls the verified \
      RC2 key expansion, saving `ebx` and `esi` in the scratch space beyond its own."])
    code := Impl.Rc2.X86.Stream.init
    contract := Spec.Rc2.cbcInitContract X86.abi 24
    stack := 24
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcInitContract; rfl⟩
    verified := Proof.Rc2.X86.Stream.init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Rc2.cbcEncryptUpdateApi with
    target := X86.target
    doc := Spec.Rc2.cbcEncryptUpdateApi.doc (notes := ["Baseline x86: copies bytes one at a time and \
      calls the verified RC2-CBC encryption on the output in place."])
    code := Impl.Rc2.X86.Stream.encryptUpdate
    contract := Spec.Rc2.cbcEncryptUpdateContract X86.abi 40
    stack := 40
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcEncryptUpdateContract Spec.Rc2.cbcUpdateContract; rfl⟩
    verified := Proof.Rc2.X86.Stream.encryptUpdate_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Rc2.cbcDecryptUpdateApi with
    target := X86.target
    doc := Spec.Rc2.cbcDecryptUpdateApi.doc (notes := ["Baseline x86: copies bytes one at a time and \
      calls the verified RC2-CBC decryption on the output in place."])
    code := Impl.Rc2.X86.Stream.decryptUpdate
    contract := Spec.Rc2.cbcDecryptUpdateContract X86.abi 40
    stack := 40
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcDecryptUpdateContract Spec.Rc2.cbcUpdateContract; rfl⟩
    verified := Proof.Rc2.X86.Stream.decryptUpdate_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
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

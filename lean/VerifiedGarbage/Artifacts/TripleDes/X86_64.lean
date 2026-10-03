import VerifiedGarbage.Proof.TripleDes.X86_64.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Verified

namespace VG.Artifacts.TripleDes.X86_64

def artifacts : List Artifact := [
  { Spec.TripleDes.expandKeyApi with
    target := X86_64.target
    doc := Spec.TripleDes.expandKeyApi.doc
      (notes := ["Baseline x86-64 scalar key expansion with fixed permutations and public round-count branches."])
    code := Impl.TripleDes.X86_64.Key.expandKey
    contract := Spec.TripleDes.expandKeyContract X86_64.abi
    stack := 0
    verified := Proof.TripleDes.X86_64.Key.verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.encryptBlockApi with
    target := X86_64.target
    doc := Spec.TripleDes.encryptBlockApi.doc
      (notes := ["Baseline x86-64 scalar Boolean S-box circuits; IP and FP shared across all three DES passes."])
    code := Impl.TripleDes.X86_64.encryptBlock
    contract := Spec.TripleDes.encryptBlockContract X86_64.abi
    stack := 0
    verified := Proof.TripleDes.X86_64.encrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.decryptBlockApi with
    target := X86_64.target
    doc := Spec.TripleDes.decryptBlockApi.doc
      (notes := ["Baseline x86-64 scalar Boolean S-box circuits with reverse EDE key order."])
    code := Impl.TripleDes.X86_64.decryptBlock
    contract := Spec.TripleDes.decryptBlockContract X86_64.abi
    stack := 0
    verified := Proof.TripleDes.X86_64.decrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.ecbEncryptApi with
    target := X86_64.target
    doc := Spec.TripleDes.ecbEncryptApi.doc
      (notes := ["Bitsliced on baseline x86-64: 64 blocks at a time, one in each bit position of 64 state words, through Boolean S-box circuits."])
    code := Impl.TripleDes.X86_64.Bitslice.encrypt
    contract := Spec.TripleDes.ecbEncryptContract X86_64.abi
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbEncryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.X86_64.Bitsliced.encrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.ecbDecryptApi with
    target := X86_64.target
    doc := Spec.TripleDes.ecbDecryptApi.doc
      (notes := ["Bitsliced on baseline x86-64: 64 blocks at a time, one in each bit position of 64 state words, through Boolean S-box circuits."])
    code := Impl.TripleDes.X86_64.Bitslice.decrypt
    contract := Spec.TripleDes.ecbDecryptContract X86_64.abi
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbDecryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.X86_64.Bitsliced.decrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.TripleDes.X86_64

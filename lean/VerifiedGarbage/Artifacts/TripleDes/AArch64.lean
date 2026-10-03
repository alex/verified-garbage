import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Verified

namespace VG.Artifacts.TripleDes.AArch64

def artifacts : List Artifact := [
  { Spec.TripleDes.expandKeyApi with
    target := AArch64.target
    doc := Spec.TripleDes.expandKeyApi.doc
      (notes := ["Baseline AArch64 scalar key expansion with fixed permutations and public round-count branches."])
    code := Impl.TripleDes.AArch64.Key.expandKey
    contract := Spec.TripleDes.expandKeyContract AArch64.abi
    stack := 0
    verified := Proof.TripleDes.AArch64.Key.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.encryptBlockApi with
    target := AArch64.target
    doc := Spec.TripleDes.encryptBlockApi.doc
      (notes := ["Baseline AArch64 scalar Boolean S-box circuits; IP and FP shared across all three DES passes."])
    code := Impl.TripleDes.AArch64.encryptBlock
    contract := Spec.TripleDes.encryptBlockContract AArch64.abi
    stack := 0
    verified := Proof.TripleDes.AArch64.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.decryptBlockApi with
    target := AArch64.target
    doc := Spec.TripleDes.decryptBlockApi.doc
      (notes := ["Baseline AArch64 scalar Boolean S-box circuits with reverse EDE key order."])
    code := Impl.TripleDes.AArch64.decryptBlock
    contract := Spec.TripleDes.decryptBlockContract AArch64.abi
    stack := 0
    verified := Proof.TripleDes.AArch64.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.ecbEncryptApi with
    target := AArch64.target
    doc := Spec.TripleDes.ecbEncryptApi.doc
      (notes := ["Bitsliced in AdvSIMD registers: 128 blocks at a time, in place in the data, in 128-bit words, through Boolean S-box circuits; the blocks left after the last 128 through the scratch buffer."])
    code := Impl.TripleDes.AArch64.BitsliceNeon.encrypt
    contract := Spec.TripleDes.ecbEncryptContract AArch64.abi 0
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbEncryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.AArch64.BitslicedNeon.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.ecbDecryptApi with
    target := AArch64.target
    doc := Spec.TripleDes.ecbDecryptApi.doc
      (notes := ["Bitsliced in AdvSIMD registers: 128 blocks at a time, in place in the data, in 128-bit words, through Boolean S-box circuits; the blocks left after the last 128 through the scratch buffer."])
    code := Impl.TripleDes.AArch64.BitsliceNeon.decrypt
    contract := Spec.TripleDes.ecbDecryptContract AArch64.abi 0
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbDecryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.AArch64.BitslicedNeon.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.TripleDes.AArch64

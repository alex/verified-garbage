import VerifiedGarbage.Proof.CmacAes.AArch64.Aese
namespace VG.Artifacts.CmacAes.AArch64
def artifacts : List Artifact := [
  { Spec.Cmac.aesUpdateApi with
    name := "vg_cmac_aes_update_aes_cbc"
    target := AArch64.target
    doc := Spec.Cmac.aesUpdateApi.doc (notes := [
      "The round keys and chaining value stay in vector registers across all blocks. \
      The first and last round keys are folded into the input, and the round count is selected once. \
      No stack or scratch space is used."])
    code := Impl.CmacAes.AArch64.Aese.update
    contract := Spec.Cmac.aesUpdateContract AArch64.abi
    verified := Proof.CmacAes.AArch64.Aese.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := ["aes"] }]
end VG.Artifacts.CmacAes.AArch64

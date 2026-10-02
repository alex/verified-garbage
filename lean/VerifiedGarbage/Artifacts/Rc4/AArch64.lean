import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedInit
import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedApply

/-! # Raw RC4 on baseline AArch64 -/
namespace VG.Artifacts.Rc4.AArch64

def artifacts : List Artifact := [
  { Spec.Rc4.initApi with
    target := AArch64.target
    doc := Spec.Rc4.initApi.doc (notes := [
      "Secret-indexed table operations visit every 16-byte row at fixed addresses, \
       using NEON register-table lookups and masked replacement."])
    code := Impl.Rc4.AArch64.init
    contract := Spec.Rc4.initContract AArch64.abi
    verified := Proof.Rc4.AArch64.init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc4.applyApi with
    target := AArch64.target
    doc := Spec.Rc4.applyApi.doc (notes := [
      "Secret-indexed table operations visit every 16-byte row at fixed addresses, \
       using NEON register-table lookups and masked replacement."])
    code := Impl.Rc4.AArch64.apply
    contract := Spec.Rc4.applyContract AArch64.abi
    verified := Proof.Rc4.AArch64.apply_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Rc4.AArch64

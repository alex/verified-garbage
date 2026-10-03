import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Rc4.X86_64.Verified

/-! # Raw RC4 on baseline x86-64 -/
namespace VG.Artifacts.Rc4.X86_64

def artifacts : List Artifact := [
  { Spec.Rc4.initApi with
    target := X86_64.target
    doc := Spec.Rc4.initApi.doc (notes := [
      "Secret-indexed table operations visit every quadword of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `sub` and `sbb`."])
    code := Impl.Rc4.X86_64.init
    contract := Spec.Rc4.initContract X86_64.abi
    verified := Proof.Rc4.X86_64.init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Rc4.applyApi with
    target := X86_64.target
    doc := Spec.Rc4.applyApi.doc (notes := [
      "Secret-indexed table operations visit every quadword of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `sub` and `sbb`."])
    code := Impl.Rc4.X86_64.apply
    contract := Spec.Rc4.applyContract X86_64.abi
    verified := Proof.Rc4.X86_64.apply_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Rc4.X86_64

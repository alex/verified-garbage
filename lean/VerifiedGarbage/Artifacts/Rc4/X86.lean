import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Rc4.X86.Verified

/-! # Raw RC4 on baseline x86 -/
namespace VG.Artifacts.Rc4.X86

def artifacts : List Artifact := [
  { Spec.Rc4.initApi with
    target := X86.target
    doc := Spec.Rc4.initApi.doc (notes := [
      "Secret-indexed table operations visit every doubleword of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `sub` and `sbb`. Our caller's `ebx`, \
       `esi`, `edi` and `ebp` are saved in `scratch`."])
    code := Impl.Rc4.X86.init
    contract := Spec.Rc4.initContract X86.abi
    stack := 0
    verified := Proof.Rc4.X86.init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Rc4.applyApi with
    target := X86.target
    doc := Spec.Rc4.applyApi.doc (notes := [
      "Secret-indexed table operations visit every doubleword of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `sub` and `sbb`. Our caller's `ebx`, \
       `esi`, `edi` and `ebp` are saved in `scratch`, and `j` is kept there during each \
       keystream lookup."])
    code := Impl.Rc4.X86.apply
    contract := Spec.Rc4.applyContract X86.abi
    stack := 0
    verified := Proof.Rc4.X86.apply_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Rc4.X86

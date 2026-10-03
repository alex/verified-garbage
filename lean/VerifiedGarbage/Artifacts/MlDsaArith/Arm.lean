import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttInv

/-! # ML-DSA (FIPS 204) on 32-bit ARM: the arithmetic of polynomials -/

namespace VG.Artifacts.MlDsaArith.Arm

def artifacts : List Artifact := [
  { Spec.MlDsa.nttApi with
    target := Arm.target
    doc := Spec.MlDsa.nttApi.doc
      (notes := ["The function saves `r4`–`r10` on the stack (the 28 bytes below the stack pointer), and \
        stores a table of the 256 zetas in `scratch`."])
    code := Impl.MlDsa.Arm.Arith.ntt
    contract := Spec.MlDsa.nttContract Arm.abi 28
    stack := 28
    verified := Proof.MlDsa.Arm.Arith.Ntt.verified
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract; exact rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.nttInvApi with
    target := Arm.target
    doc := Spec.MlDsa.nttInvApi.doc
      (notes := ["The function saves `r4`–`r10` on the stack (the 28 bytes below the stack pointer), and \
        stores a table of the 256 negated zetas in `scratch`."])
    code := Impl.MlDsa.Arm.Arith.nttInv
    contract := Spec.MlDsa.nttInvContract Arm.abi 28
    stack := 28
    verified := Proof.MlDsa.Arm.Arith.NttInv.verified
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract; exact rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.mulApi with
    target := Arm.target
    doc := Spec.MlDsa.mulApi.doc
      (notes := ["The function saves `r4`–`r9` on the stack (the 24 bytes below the stack pointer)."])
    code := Impl.MlDsa.Arm.Arith.mul
    contract := Spec.MlDsa.mulContract Arm.abi 24
    stack := 24
    verified := Proof.MlDsa.Arm.Arith.Mul.mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.mulAddApi with
    target := Arm.target
    doc := Spec.MlDsa.mulAddApi.doc
      (notes := ["The function saves `r4`–`r9` on the stack (the 24 bytes below the stack pointer)."])
    code := Impl.MlDsa.Arm.Arith.mulAdd
    contract := Spec.MlDsa.mulAddContract Arm.abi 24
    stack := 24
    verified := Proof.MlDsa.Arm.Arith.Mul.mulAdd_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.addApi with
    target := Arm.target
    doc := Spec.MlDsa.addApi.doc
    code := Impl.MlDsa.Arm.Arith.add
    contract := Spec.MlDsa.addContract Arm.abi
    verified := Proof.MlDsa.Arm.Arith.AddSub.add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.subApi with
    target := Arm.target
    doc := Spec.MlDsa.subApi.doc
    code := Impl.MlDsa.Arm.Arith.sub
    contract := Spec.MlDsa.subContract Arm.abi
    verified := Proof.MlDsa.Arm.Arith.AddSub.sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaArith.Arm

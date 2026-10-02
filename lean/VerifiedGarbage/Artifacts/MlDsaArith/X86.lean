import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlDsa.X86.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv

/-!
# ML-DSA (FIPS 204) on x86: the arithmetic of polynomials

The functions call no other one, and save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
-/

namespace VG.Artifacts.MlDsaArith.X86

def artifacts : List Artifact := [
  { Spec.MlDsa.nttApi with
    target := X86.target
    doc := Spec.MlDsa.nttApi.doc
      (notes := ["The function stores a table of the 256 zetas, in Montgomery form, in `scratch`."])
    code := Impl.MlDsa.X86.Arith.ntt
    contract := Spec.MlDsa.nttContract X86.abi 16
    stack := 16
    verified := Proof.MlDsa.X86.Arith.NttFwd.verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.nttInvApi with
    target := X86.target
    doc := Spec.MlDsa.nttInvApi.doc
      (notes := ["The function stores a table of the 256 negated zetas, in Montgomery form, in `scratch`."])
    code := Impl.MlDsa.X86.Arith.nttInv
    contract := Spec.MlDsa.nttInvContract X86.abi 16
    stack := 16
    verified := Proof.MlDsa.X86.Arith.NttInvP.verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.mulApi with
    target := X86.target
    doc := Spec.MlDsa.mulApi.doc
    code := Impl.MlDsa.X86.Arith.mul
    contract := Spec.MlDsa.mulContract X86.abi 16
    stack := 16
    verified := Proof.MlDsa.X86.Arith.mul_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlDsa.mulAddApi with
    target := X86.target
    doc := Spec.MlDsa.mulAddApi.doc
    code := Impl.MlDsa.X86.Arith.mulAdd
    contract := Spec.MlDsa.mulAddContract X86.abi 16
    stack := 16
    verified := Proof.MlDsa.X86.Arith.mulAdd_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlDsa.addApi with
    target := X86.target
    doc := Spec.MlDsa.addApi.doc
    code := Impl.MlDsa.X86.Arith.add
    contract := Spec.MlDsa.addContract X86.abi 16
    stack := 16
    verified := Proof.MlDsa.X86.Arith.add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlDsa.subApi with
    target := X86.target
    doc := Spec.MlDsa.subApi.doc
    code := Impl.MlDsa.X86.Arith.sub
    contract := Spec.MlDsa.subContract X86.abi 16
    stack := 16
    verified := Proof.MlDsa.X86.Arith.sub_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.MlDsaArith.X86

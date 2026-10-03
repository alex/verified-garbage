import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inst

/-! # ML-DSA (FIPS 204) key generation on 32-bit ARM -/

namespace VG.Artifacts.MlDsaKeyGen.Arm

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers and `lr` in `scratch`; the functions it \
    calls use the 36 bytes of stack below the stack pointer.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def artifacts : List Artifact := [
  { Spec.MlDsa.keyGen44Api with
    target := Arm.target
    doc := Spec.MlDsa.keyGen44Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.KeyGen.keyGen44
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.KeyGen.keyGen44_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.keyGen65Api with
    target := Arm.target
    doc := Spec.MlDsa.keyGen65Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.KeyGen.keyGen65
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.KeyGen.keyGen65_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.keyGen87Api with
    target := Arm.target
    doc := Spec.MlDsa.keyGen87Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.KeyGen.keyGen87
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.KeyGen.keyGen87_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaKeyGen.Arm

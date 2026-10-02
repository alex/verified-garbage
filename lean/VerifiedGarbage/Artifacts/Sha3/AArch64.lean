import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorPermute
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze

/-! # SHA-3 and SHAKE (FIPS 202) on AArch64 -/

namespace VG.Artifacts.Sha3.AArch64

def artifacts : List Artifact := [
  { Spec.Sha3.permuteApi with
    name := "vg_keccak_f1600_sha3"
    target := AArch64.target
    doc := Spec.Sha3.permuteApi.doc (notes := ["Uses the Arm SHA-3 instructions."])
    code := Impl.Sha3.AArch64.Sha3.Vector.permute
    contract := Spec.Sha3.permuteContract AArch64.abi
    verified := Proof.Sha3.AArch64.Sha3.Vector.permute_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := ["sha3"] },
  { Spec.Sha3.permuteApi with
    target := AArch64.target
    doc := Spec.Sha3.permuteApi.doc
    code := Impl.Sha3.AArch64.Scalar.vectorPermute
    contract := Spec.Sha3.permuteContract AArch64.abi
    verified := Proof.Sha3.AArch64.Scalar.vector_permute_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha3.AArch64

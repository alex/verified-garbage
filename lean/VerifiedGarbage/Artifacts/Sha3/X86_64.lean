import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze

/-! # SHA-3 and SHAKE (FIPS 202) on x86-64 -/

namespace VG.Artifacts.Sha3.X86_64

def artifacts : List Artifact := [
  { Spec.Sha3.permuteApi with
    target := X86_64.target
    doc := Spec.Sha3.permuteApi.doc
    code := Impl.Sha3.X86_64.permute
    contract := Spec.Sha3.permuteContract X86_64.abi
    verified := Proof.Sha3.X86_64.permute_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha3.absorbApi with
    target := X86_64.target
    doc := Spec.Sha3.absorbApi.doc
    code := Impl.Sha3.X86_64.Stream.absorb
    contract := Spec.Sha3.absorbContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha3.X86_64.Stream.Absorb.absorb_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha3.padApi with
    target := X86_64.target
    doc := Spec.Sha3.padApi.doc
    code := Impl.Sha3.X86_64.Stream.pad
    contract := Spec.Sha3.padContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha3.X86_64.Stream.Pad.pad_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha3.squeezeApi with
    target := X86_64.target
    doc := Spec.Sha3.squeezeApi.doc
    code := Impl.Sha3.X86_64.Stream.squeeze
    contract := Spec.Sha3.squeezeContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha3.X86_64.Stream.Squeeze.squeeze_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha3.X86_64

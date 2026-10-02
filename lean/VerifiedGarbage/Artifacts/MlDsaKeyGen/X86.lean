import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inst

/-!
# ML-DSA (FIPS 204) key generation on x86 (32-bit)

The functions save their caller's registers in a frame of 16 bytes below
the return address; their calls of the primitives use the 80 bytes below
it: at most 5 arguments, the return address and the primitive's 56 bytes
(`stack := 96`).
-/

namespace VG.Artifacts.MlDsaKeyGen.X86

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in a frame of 16 bytes; its calls use \
    the 80 bytes of stack below it.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def artifacts : List Artifact := [
  { Spec.MlDsa.keyGen44Api with
    target := X86.target
    doc := Spec.MlDsa.keyGen44Api.doc (notes := notes)
    code := Impl.MlDsa.X86.KeyGen.keyGen44
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 X86.abi 96
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen44_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.keyGen65Api with
    target := X86.target
    doc := Spec.MlDsa.keyGen65Api.doc (notes := notes)
    code := Impl.MlDsa.X86.KeyGen.keyGen65
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 X86.abi 96
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen65_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.keyGen87Api with
    target := X86.target
    doc := Spec.MlDsa.keyGen87Api.doc (notes := notes)
    code := Impl.MlDsa.X86.KeyGen.keyGen87
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 X86.abi 96
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen87_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaKeyGen.X86

import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha256.X86_64.Shared

/-! # SHA-256 (FIPS 180-4) on x86-64 -/

namespace VG.Artifacts.Sha256.X86_64

def artifacts : List Artifact := [
  { Spec.Sha256.compressApi with
    target := X86_64.target
    doc := Spec.Sha256.compressApi.doc
    code := Impl.Sha256.X86_64.compress
    contract := Spec.Sha256.compressContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.compress
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha256.initApi with
    target := X86_64.target
    doc := Spec.Sha256.initApi.doc
    code := Impl.Sha256.X86_64.Stream.init
    contract := Spec.Sha256.initContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha256.compressApi with
    name := "vg_sha256_compress_shani"
    target := X86_64.target
    doc := Spec.Sha256.compressApi.doc
      (notes := ["This implementation uses the SHA extensions."])
    code := Impl.Sha256.X86_64.ShaNi.compress
    contract := Spec.Sha256.compressContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.compress_shani
    features := ["sha", "ssse3"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha256.compressApi with
    name := "vg_sha256_compress_avx2"
    target := X86_64.target
    doc := Spec.Sha256.compressApi.doc
      (notes := ["This implementation computes the message schedules of two blocks at a time in \
        the two lanes of the AVX2 registers, and the rounds with BMI1 and BMI2."])
    code := Impl.Sha256.X86_64.Avx2.compress
    contract := Spec.Sha256.compressContract X86_64.abi
    verified := Proof.Sha256.X86_64.Shared.compress_avx2
    features := ["avx", "avx2", "bmi1", "bmi2"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha256.X86_64

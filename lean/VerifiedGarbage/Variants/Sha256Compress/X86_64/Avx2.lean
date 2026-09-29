import VerifiedGarbage.Proof.Sha256.X86_64.Variant
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Compress

/-!
# SHA-256 compression on x86-64 with AVX2 and BMI

A variant of `Sha256Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_sha256_compress_avx2`, which needs AVX, AVX2, BMI1 and BMI2.
-/

namespace VG.Variants.Sha256Compress.X86_64.Avx2

open VG.Impl.Sha256.X86_64.Stream (Callee)

theorem ok : Callee.avx2.Ok :=
  .of_verified Proof.Sha256.X86_64.Avx2.compress_verified.1
    Proof.Sha256.X86_64.Avx2.compress_verified.2.1 (by rw [← Code.allInstrs_eq]; decide +kernel)
    (by decide +kernel)

def variant : Proof.Sha256.X86_64.Compress where
  callee := .avx2
  ok := ok
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := "_avx2"
  features := ["avx", "avx2", "bmi1", "bmi2"]

end VG.Variants.Sha256Compress.X86_64.Avx2

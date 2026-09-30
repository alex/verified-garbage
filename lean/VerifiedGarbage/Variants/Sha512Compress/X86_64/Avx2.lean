import VerifiedGarbage.Proof.Sha512.X86_64.Variant

/-!
# SHA-512 compression on x86-64 with AVX2 and BMI

A variant of `Sha512Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_sha512_compress_avx2`, which needs AVX, AVX2, BMI1 and BMI2.
-/

namespace VG.Variants.Sha512Compress.X86_64.Avx2

def variant : Proof.Sha512.X86_64.Compress where
  callee := .avx2
  ok := Proof.Sha512.X86_64.Stream.avx2_ok
  mxcsr := by change Impl.Sha512.X86_64.Avx2.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.Avx2.compress.allInstrs _ = true; lit_decide)
  suffix := "_avx2"
  features := ["avx", "avx2", "bmi1", "bmi2"]

end VG.Variants.Sha512Compress.X86_64.Avx2

import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
import VerifiedGarbage.Variants.MdHash.X86_64.Sha256Avx2

/-!
# SHA-224 on x86-64 with AVX2 and BMI

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): SHA-224, with `vg_sha256_compress_avx2`,
which needs AVX, AVX2, BMI1 and BMI2 (`Variants/MdHash/X86_64/Sha256Avx2.lean`).
-/

namespace VG.Variants.MdHash.X86_64.Sha224Avx2

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha224.variant Variants.MdHash.X86_64.Sha256Avx2.compress

end VG.Variants.MdHash.X86_64.Sha224Avx2

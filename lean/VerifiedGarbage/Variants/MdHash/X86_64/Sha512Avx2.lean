import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512

/-!
# SHA-512 on x86-64 with AVX2 and BMI

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): SHA-512, with
`vg_sha512_compress_avx2`, which needs AVX, AVX2, BMI1 and BMI2.

It carries the streaming `update` and `finalize` made with it, which the
family shares.
-/

namespace VG.Variants.MdHash.X86_64.Sha512Avx2

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512 .avx2 (Proof.Pbkdf2.Md.X86_64.Sha512.stream .avx2)

end VG.Variants.MdHash.X86_64.Sha512Avx2

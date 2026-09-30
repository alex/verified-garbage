import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl

/-!
# `vg_mlkem_sample_ntt4` on x86-64: with AVX2

A variant of `MlKemSample4` on x86-64 (see `TCB/Emit.lean`):
`vg_mlkem_sample_ntt4_avx2`, which runs the four instances of SHAKE128 at
once in AVX2 registers, and needs AVX and AVX2.
-/

namespace VG.Variants.MlKemSample4.X86_64.Avx2

def variant : Proof.MlKem.X86_64.Sample4Impl := .avx2

end VG.Variants.MlKemSample4.X86_64.Avx2

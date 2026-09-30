import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl

/-!
# `vg_mlkem_sample_ntt4` on x86-64: the baseline

A variant of `MlKemSample4` on x86-64 (see `TCB/Emit.lean`):
`vg_mlkem_sample_ntt4`, which calls `vg_mlkem_sample_ntt` on each seed.
-/

namespace VG.Variants.MlKemSample4.X86_64.Scalar

def variant : Proof.MlKem.X86_64.Sample4Impl := .scalar

end VG.Variants.MlKemSample4.X86_64.Scalar

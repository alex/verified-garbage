import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend

/-!
# ML-DSA's polynomial arithmetic on x86-64: SSE2

A variant of `MlDsaArith` on x86-64 (see `TCB/Emit.lean`): `vg_mldsa_ntt`,
`vg_mldsa_inv_ntt`, `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt`,
`vg_mldsa_add` and `vg_mldsa_sub`, in the baseline ISA (SSE2), which key
generation, signing and verification call.
-/

namespace VG.Variants.MlDsaArith.X86_64.Sse2

def variant : Proof.MlDsa.X86_64.ArithImpl := .sse2

end VG.Variants.MlDsaArith.X86_64.Sse2

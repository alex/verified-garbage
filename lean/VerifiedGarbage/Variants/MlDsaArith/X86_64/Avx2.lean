import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.BackendAvx2

/-!
# ML-DSA's polynomial arithmetic on x86-64: AVX2

A variant of `MlDsaArith` on x86-64 (see `TCB/Emit.lean`):
`vg_mldsa_ntt_avx2`, `vg_mldsa_inv_ntt_avx2`,
`vg_mldsa_multiply_ntt_avx2`, `vg_mldsa_multiply_add_ntt_avx2`,
`vg_mldsa_add_avx2`, `vg_mldsa_sub_avx2`, `vg_mldsa_high_bits_avx2`,
`vg_mldsa_low_bits_avx2`, `vg_mldsa_norm_lt_avx2` and
`vg_mldsa_make_hint_avx2`, on eight coefficients at a time in AVX2
registers, which need AVX and AVX2; key generation, signing and
verification calling them need them too.
-/

namespace VG.Variants.MlDsaArith.X86_64.Avx2

def variant : Proof.MlDsa.X86_64.ArithImpl := .avx2

end VG.Variants.MlDsaArith.X86_64.Avx2

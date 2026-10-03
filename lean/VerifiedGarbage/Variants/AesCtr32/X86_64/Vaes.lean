import VerifiedGarbage.Proof.Aes.X86_64.Variant

/-!
# `vg_aes_ctr32` on x86-64: with VAES

A variant of `AesCtr32` on x86-64 (see `TCB/Emit.lean`):
`vg_aes_ctr32_vaes`, which needs VAES and AVX2 (and AES-NI and SSSE3).
-/

namespace VG.Variants.AesCtr32.X86_64.Vaes

def variant : Proof.Aes.X86_64.Ctr32Impl := .vaes

end VG.Variants.AesCtr32.X86_64.Vaes

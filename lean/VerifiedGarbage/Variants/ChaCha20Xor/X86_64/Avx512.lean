import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant

/-!
# `vg_chacha20_xor` on x86-64: with AVX-512

A variant of `ChaCha20Xor` on x86-64 (see `TCB/Emit.lean`):
`vg_chacha20_xor_avx512`, which needs AVX and AVX-512F.
-/

namespace VG.Variants.ChaCha20Xor.X86_64.Avx512

def variant : Proof.ChaCha20.X86_64.XorImpl := .avx512

end VG.Variants.ChaCha20Xor.X86_64.Avx512

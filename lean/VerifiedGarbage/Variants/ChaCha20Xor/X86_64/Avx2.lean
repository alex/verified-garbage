import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant

/-!
# `vg_chacha20_xor` on x86-64: with AVX2

A variant of `ChaCha20Xor` on x86-64 (see `TCB/Emit.lean`):
`vg_chacha20_xor_avx2`, which needs AVX and AVX2.
-/

namespace VG.Variants.ChaCha20Xor.X86_64.Avx2

def variant : Proof.ChaCha20.X86_64.XorImpl := .avx2

end VG.Variants.ChaCha20Xor.X86_64.Avx2

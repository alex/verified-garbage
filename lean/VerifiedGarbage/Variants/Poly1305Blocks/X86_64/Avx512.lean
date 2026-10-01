import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Variant

/-!
# `vg_poly1305_blocks` on x86-64: with AVX-512

A variant of `Poly1305Blocks` on x86-64 (see `TCB/Emit.lean`):
`vg_poly1305_blocks_avx512`, which needs AVX, AVX-512F and AVX2.
-/

namespace VG.Variants.Poly1305Blocks.X86_64.Avx512

def variant : Proof.Poly1305.X86_64.BlocksImpl := .avx512

end VG.Variants.Poly1305Blocks.X86_64.Avx512

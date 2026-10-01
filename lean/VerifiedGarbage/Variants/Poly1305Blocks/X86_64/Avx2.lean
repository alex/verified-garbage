import VerifiedGarbage.Proof.Poly1305.X86_64.Variant

/-!
# `vg_poly1305_blocks` on x86-64: with AVX2

A variant of `Poly1305Blocks` on x86-64 (see `TCB/Emit.lean`):
`vg_poly1305_blocks_avx2`, which needs AVX and AVX2.
-/

namespace VG.Variants.Poly1305Blocks.X86_64.Avx2

def variant : Proof.Poly1305.X86_64.BlocksImpl := .avx2

end VG.Variants.Poly1305Blocks.X86_64.Avx2

import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant

/-!
# `vg_chacha20_xor` on x86-64: the scalar implementation

A variant of `ChaCha20Xor` on x86-64 (see `TCB/Emit.lean`):
`vg_chacha20_xor`, in the baseline ISA.
-/

namespace VG.Variants.ChaCha20Xor.X86_64.Scalar

def variant : Proof.ChaCha20.X86_64.XorImpl := .scalar

end VG.Variants.ChaCha20Xor.X86_64.Scalar

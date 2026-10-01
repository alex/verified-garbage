import VerifiedGarbage.Proof.Aes.X86_64.Variant

/-!
# `vg_aes_ctr32` on x86-64: the bitsliced implementation

A variant of `AesCtr32` on x86-64 (see `TCB/Emit.lean`): `vg_aes_ctr32`, in
the baseline ISA.
-/

namespace VG.Variants.AesCtr32.X86_64.Scalar

def variant : Proof.Aes.X86_64.Ctr32Impl := .scalar

end VG.Variants.AesCtr32.X86_64.Scalar

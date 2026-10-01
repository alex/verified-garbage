import VerifiedGarbage.Proof.Aes.AArch64.Variant

/-!
# `vg_aes_ctr32` on AArch64: the bitsliced implementation

A variant of `AesCtr32` on AArch64 (see `TCB/Emit.lean`): `vg_aes_ctr32`, in
the baseline ISA.
-/

namespace VG.Variants.AesCtr32.AArch64.Scalar

def variant : Proof.Aes.AArch64.Ctr32Impl := .scalar

end VG.Variants.AesCtr32.AArch64.Scalar

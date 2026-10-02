import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-!
# The functions AES-GCM calls on AArch64: Scalar

A variant of `AesGcm` on AArch64 (see `TCB/Emit.lean`): the baseline ISA for
the cipher (`vg_aes_ctr32`, `vg_aes_expand_key`) and the hash (`vg_ghash`).
-/

namespace VG.Variants.AesGcm.AArch64.Scalar

def variant : Proof.AesGcm.AArch64.GcmImpl := ⟨.scalar, .scalar, .scalar⟩

end VG.Variants.AesGcm.AArch64.Scalar

import VerifiedGarbage.Proof.AesGcm.X86.Callee

/-!
# The functions AES-GCM calls on x86: Scalar

A variant of `AesGcm` on x86 (see `TCB/Emit.lean`): the baseline ISA: `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`.
-/

namespace VG.Variants.AesGcm.X86.Scalar

def variant : Proof.AesGcm.X86.GcmImpl := ⟨.scalar, .scalar⟩

end VG.Variants.AesGcm.X86.Scalar

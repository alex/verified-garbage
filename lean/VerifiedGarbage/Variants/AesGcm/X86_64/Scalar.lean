import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# The functions AES-GCM calls on x86-64: Scalar

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): the baseline ISA: `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`.
-/

namespace VG.Variants.AesGcm.X86_64.Scalar

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.scalar, .scalar, .scalar, false, nofun⟩

end VG.Variants.AesGcm.X86_64.Scalar

import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls

/-!
# The functions AES-GCM calls on x86: Pclmul

A variant of `AesGcm` on x86 (see `TCB/Emit.lean`): `vg_aes_ctr32` and `vg_aes_expand_key`, and PCLMULQDQ for the hash (`vg_ghash_pclmul`).
-/

namespace VG.Variants.AesGcm.X86.Pclmul

def variant : Proof.AesGcm.X86.GcmImpl := ⟨.scalar, .pclmul⟩

end VG.Variants.AesGcm.X86.Pclmul

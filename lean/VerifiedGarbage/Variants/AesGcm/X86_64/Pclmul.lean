import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# The functions AES-GCM calls on x86-64: Pclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): `vg_aes_ctr32` and `vg_aes_expand_key`, and PCLMULQDQ for the hash (`vg_ghash_pclmul`).
-/

namespace VG.Variants.AesGcm.X86_64.Pclmul

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.scalar, .scalar, .pclmul, false, nofun⟩

end VG.Variants.AesGcm.X86_64.Pclmul

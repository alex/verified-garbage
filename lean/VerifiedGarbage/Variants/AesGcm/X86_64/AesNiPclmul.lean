import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# The functions AES-GCM calls on x86-64: AesNiPclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): AES-NI for the cipher (`vg_aes_ctr32_aesni`, `vg_aes_expand_key_aesni`) and PCLMULQDQ for the hash (`vg_ghash_pclmul`).
-/

namespace VG.Variants.AesGcm.X86_64.AesNiPclmul

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.aesni, .aesni, .pclmul⟩

end VG.Variants.AesGcm.X86_64.AesNiPclmul

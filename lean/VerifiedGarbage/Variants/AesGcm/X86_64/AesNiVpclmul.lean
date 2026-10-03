import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# The functions AES-GCM calls on x86-64: AesNiVpclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): AES-NI for the cipher (`vg_aes_ctr32_aesni`, `vg_aes_expand_key_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`).
-/

namespace VG.Variants.AesGcm.X86_64.AesNiVpclmul

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.aesni, .aesni, .vpclmul⟩

end VG.Variants.AesGcm.X86_64.AesNiVpclmul

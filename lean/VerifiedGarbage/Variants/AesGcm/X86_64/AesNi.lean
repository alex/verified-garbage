import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-!
# The functions AES-GCM calls on x86-64: AesNi

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): AES-NI for the cipher (`vg_aes_ctr32_aesni`, `vg_aes_expand_key_aesni`) and `vg_ghash`.
-/

namespace VG.Variants.AesGcm.X86_64.AesNi

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.aesni, .aesni, .scalar⟩

end VG.Variants.AesGcm.X86_64.AesNi

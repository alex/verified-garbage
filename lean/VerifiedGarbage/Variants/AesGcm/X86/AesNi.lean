import VerifiedGarbage.Proof.AesGcm.X86.Callee

/-!
# The functions AES-GCM calls on x86: AesNi

A variant of `AesGcm` on x86 (see `TCB/Emit.lean`): AES-NI for the cipher (`vg_aes_ctr32_aesni`, `vg_aes_expand_key_aesni`) and `vg_ghash`.
-/

namespace VG.Variants.AesGcm.X86.AesNi

def variant : Proof.AesGcm.X86.GcmImpl := ⟨.aesni, .scalar⟩

end VG.Variants.AesGcm.X86.AesNi

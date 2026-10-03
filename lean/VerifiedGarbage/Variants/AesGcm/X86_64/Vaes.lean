import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# The functions AES-GCM calls on x86-64: Vaes

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_aesni`) and `vg_ghash`.
-/

namespace VG.Variants.AesGcm.X86_64.Vaes

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.vaes, .aesni, .scalar⟩

end VG.Variants.AesGcm.X86_64.Vaes

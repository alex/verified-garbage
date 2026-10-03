import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# The functions AES-GCM calls on x86-64: VaesPclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_aesni`) and PCLMULQDQ for the hash (`vg_ghash_pclmul`).
-/

namespace VG.Variants.AesGcm.X86_64.VaesPclmul

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.vaes, .aesni, .pclmul⟩

end VG.Variants.AesGcm.X86_64.VaesPclmul

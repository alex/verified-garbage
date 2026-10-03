import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`).
-/

namespace VG.Variants.AesGcm.X86_64.VaesVpclmul

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.vaes, .aesni, .vpclmul⟩

end VG.Variants.AesGcm.X86_64.VaesVpclmul

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# The functions AES-GCM calls on x86-64: VaesVpclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): VAES for the cipher (`vg_aes_ctr32_vaes`, with `vg_aes_expand_key_aesni`) and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`), with counter mode and GHASH interleaved in `vg_aes_gcm_encrypt_blocks_vaes_vpclmul` and `_decrypt_blocks_vaes_vpclmul`.
-/

namespace VG.Variants.AesGcm.X86_64.VaesVpclmul

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.vaes, .aesni, .vpclmul, true, fun _ => Proof.Gcm.X86_64.Stitch.stitch_ok⟩

end VG.Variants.AesGcm.X86_64.VaesVpclmul

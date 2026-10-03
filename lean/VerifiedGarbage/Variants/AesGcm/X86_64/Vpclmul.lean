import VerifiedGarbage.Proof.AesGcm.X86_64.GhashVpclmul

/-!
# The functions AES-GCM calls on x86-64: Vpclmul

A variant of `AesGcm` on x86-64 (see `TCB/Emit.lean`): `vg_aes_ctr32` and `vg_aes_expand_key`, and VPCLMULQDQ for the hash (`vg_ghash_vpclmul`).
-/

namespace VG.Variants.AesGcm.X86_64.Vpclmul

def variant : Proof.AesGcm.X86_64.GcmImpl := ⟨.scalar, .scalar, .vpclmul⟩

end VG.Variants.AesGcm.X86_64.Vpclmul

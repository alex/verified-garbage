import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls

/-!
# The functions AES-GCM calls on AArch64: Aes

A variant of `AesGcm` on AArch64 (see `TCB/Emit.lean`): the AES instructions
for the cipher (`vg_aes_ctr32_aes`, `vg_aes_expand_key_aes`) and PMULL for
the hash (`vg_ghash_aes`), which need `FEAT_AES` and `FEAT_PMULL`, both
Rust's `aes` feature.
-/

namespace VG.Variants.AesGcm.AArch64.Aes

def variant : Proof.AesGcm.AArch64.GcmImpl := ⟨.aese, .aese, .aes⟩

end VG.Variants.AesGcm.AArch64.Aes

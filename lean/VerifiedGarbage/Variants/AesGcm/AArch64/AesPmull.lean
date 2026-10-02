import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-!
# The functions AES-GCM calls on AArch64: AesPmull

A variant of `AesGcm` on AArch64 (see `TCB/Emit.lean`): the AES instructions
for the cipher (`vg_aes_ctr32_aes`, `vg_aes_expand_key_aes`) and `PMULL` for
the hash (`vg_ghash_pmull`), which need `FEAT_AES` and `FEAT_PMULL`.
-/

namespace VG.Variants.AesGcm.AArch64.AesPmull

def variant : Proof.AesGcm.AArch64.GcmImpl := ⟨.aese, .aese, .pmull⟩

end VG.Variants.AesGcm.AArch64.AesPmull

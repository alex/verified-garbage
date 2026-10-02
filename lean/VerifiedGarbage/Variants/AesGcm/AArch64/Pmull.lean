import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-!
# The functions AES-GCM calls on AArch64: Pmull

A variant of `AesGcm` on AArch64 (see `TCB/Emit.lean`): `vg_aes_ctr32` and
`vg_aes_expand_key`, and `PMULL` for the hash (`vg_ghash_pmull`), which needs
`FEAT_PMULL`.
-/

namespace VG.Variants.AesGcm.AArch64.Pmull

def variant : Proof.AesGcm.AArch64.GcmImpl := ⟨.scalar, .scalar, .pmull⟩

end VG.Variants.AesGcm.AArch64.Pmull

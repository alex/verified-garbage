import VerifiedGarbage.Proof.Aes.AArch64.Variant

/-!
# `vg_aes_ctr32` on AArch64: with the Cryptographic Extension

A variant of `AesCtr32` on AArch64 (see `TCB/Emit.lean`): `vg_aes_ctr32_aes`,
which needs the AES instructions (`FEAT_AES`).
-/

namespace VG.Variants.AesCtr32.AArch64.Aese

def variant : Proof.Aes.AArch64.Ctr32Impl := .aese

end VG.Variants.AesCtr32.AArch64.Aese

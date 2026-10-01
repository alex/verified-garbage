import VerifiedGarbage.Proof.Aes.X86_64.Variant

/-!
# `vg_aes_ctr32` on x86-64: with AES-NI

A variant of `AesCtr32` on x86-64 (see `TCB/Emit.lean`):
`vg_aes_ctr32_aesni`, which needs AES-NI and SSSE3.
-/

namespace VG.Variants.AesCtr32.X86_64.AesNi

def variant : Proof.Aes.X86_64.Ctr32Impl := .aesni

end VG.Variants.AesCtr32.X86_64.AesNi

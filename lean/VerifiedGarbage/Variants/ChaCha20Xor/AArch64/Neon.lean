import VerifiedGarbage.Proof.ChaCha20.AArch64.XorBackends

namespace VG.Variants.ChaCha20Xor.AArch64.Neon

def variant : Proof.ChaCha20.AArch64.XorImpl := .neon

end VG.Variants.ChaCha20Xor.AArch64.Neon

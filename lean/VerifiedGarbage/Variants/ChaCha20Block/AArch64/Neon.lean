import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends

namespace VG.Variants.ChaCha20Block.AArch64.Neon

def variant : Proof.ChaCha20.AArch64.BlockImpl := .neon

end VG.Variants.ChaCha20Block.AArch64.Neon

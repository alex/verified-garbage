import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend

/-! Baseline ARM64 BLAKE2b streaming backend for generic callers. -/
namespace VG.Variants.Blake2b.AArch64.Scalar

def variant : Proof.Argon2.AArch64.HPrime.Backend := Proof.Argon2.AArch64.HPrime.scalar
end VG.Variants.Blake2b.AArch64.Scalar

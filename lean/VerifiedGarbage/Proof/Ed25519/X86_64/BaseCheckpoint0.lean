import VerifiedGarbage.Impl.Ed25519.X86_64.BaseCheckpoints
import VerifiedGarbage.Proof.Ed25519.ScalarMul

namespace VG.Proof.Ed25519.X86_64
open VG.Spec.Ed25519 VG.Impl.Ed25519.X86_64

theorem baseCheckpoint0_ok : powerPoint basePoint 0 = baseCheckpoint0 := by decide +kernel

end VG.Proof.Ed25519.X86_64

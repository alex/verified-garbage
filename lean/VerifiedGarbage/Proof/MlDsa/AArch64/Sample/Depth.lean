import VerifiedGarbage.Proof.Sha3.AArch64.Variant

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sample

variable (v : Proof.Sha3.AArch64.Permutation)

theorem sponge_depth (rate len : Nat) : (spongeWith v.callee rate len).aarch64Depth = 1 := by
  simp only [spongeWith, Code.aarch64Depth, v.absorb_depth, v.pad_depth, v.squeeze_depth,
    Nat.max_self, Nat.zero_max]

theorem rejNTT_depth : (rejNTTWith v.callee).aarch64Depth = 1 := by
  simp only [rejNTTWith, zeroPoly, rnLoop, rnBody, Code.aarch64Depth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

theorem rejBounded_depth : (rejBoundedWith v.callee).aarch64Depth = 1 := by
  simp only [rejBoundedWith, rbLoop, rbBody, Code.aarch64Depth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

theorem ball_depth : (sampleInBallWith v.callee).aarch64Depth = 1 := by
  simp only [sampleInBallWith, zeroPoly, bLoop, bBody, bTry, Code.aarch64Depth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

theorem expandMask_depth : (expandMaskWith v.callee).aarch64Depth = 1 := by
  simp only [expandMaskWith, expandMaskTailWith, emLoop, Code.aarch64Depth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

end VG.Proof.MlDsa.AArch64.Sample

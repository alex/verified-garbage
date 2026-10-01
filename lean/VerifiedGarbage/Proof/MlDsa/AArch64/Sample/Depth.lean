import VerifiedGarbage.Proof.Sha3.AArch64.Variant

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sample

variable (v : Proof.Sha3.AArch64.Permutation)

theorem sponge_depth (rate len : Nat) : (spongeWith v.callee rate len).fdepth = 1 := by
  simp only [spongeWith, Code.fdepth, v.absorb_depth, v.pad_depth, v.squeeze_depth,
    Nat.max_self, Nat.zero_max]

theorem rejNTT_depth : (rejNTTWith v.callee).fdepth = 1 := by
  simp only [rejNTTWith, zeroPoly, rnLoop, rnBody, Code.fdepth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

theorem rejBounded_depth : (rejBoundedWith v.callee).fdepth = 1 := by
  simp only [rejBoundedWith, rbLoop, rbBody, Code.fdepth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

theorem ball_depth : (sampleInBallWith v.callee).fdepth = 1 := by
  simp only [sampleInBallWith, zeroPoly, bLoop, bBody, bTry, Code.fdepth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

theorem expandMask_depth : (expandMaskWith v.callee).fdepth = 1 := by
  simp only [expandMaskWith, expandMaskTailWith, emLoop, Code.fdepth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

end VG.Proof.MlDsa.AArch64.Sample

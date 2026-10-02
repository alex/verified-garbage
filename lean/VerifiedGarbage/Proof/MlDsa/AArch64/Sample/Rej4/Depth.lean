import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample.Rej4

theorem rounds_depth (sha3 : Bool) (n : Nat) :
    (Impl.Sha3.AArch64.Neon.Pair.roundsProg sha3 n).aarch64Depth = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Impl.Sha3.AArch64.Neon.Pair.roundsProg,Code.aarch64Depth,ih]
    cases sha3 <;> rfl

theorem pair_depth (sha3 : Bool) (p a b : Reg) :
    (Impl.Sha3.AArch64.Neon.Pair.progWith sha3 p a b).aarch64Depth = 0 := by
  simp only [Impl.Sha3.AArch64.Neon.Pair.progWith,Code.aarch64Depth,rounds_depth,Nat.max_self]

theorem depth (sha3 : Bool) : (rejNTT4With sha3).aarch64Depth = 0 := by
  simp only [rejNTT4With,squeezeStepWith,sample,Impl.MlDsa.AArch64.Sample.zeroPoly,
    Impl.MlDsa.AArch64.Sample.rnLoop,Impl.MlDsa.AArch64.Sample.rnBody,Code.aarch64Depth,pair_depth,Nat.max_self]
end VG.Proof.MlDsa.AArch64.Sample.Rej4

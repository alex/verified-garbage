import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Sat

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

theorem signCached_implies : signCachedLocal.Implies (Spec.Ed25519.signCachedContract AArch64.abi 336) where
  pre := by
    sig_implies_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedLocal, below, AArch64.abi, AArch64.argRegs]
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedLocal, below, AArch64.abi, AArch64.argRegs]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedLocal, below, AArch64.abi, AArch64.argRegs]
  sat := sat

end VG.Proof.Ed25519.AArch64.SignCached

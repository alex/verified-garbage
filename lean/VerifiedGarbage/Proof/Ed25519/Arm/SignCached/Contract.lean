import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Sat
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Entry

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm

theorem signCached_implies : signCachedLocal.Implies (Spec.Ed25519.signCachedContract Arm.abi 280) where
  pre := by
    intro s h
    sig_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr] at h
    sig_split h
    sig_reduce [signCachedLocal, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
    sig_simp [] []
    simp only [BitVec.add_zero, show (280#64) = (280 : Addr) from rfl] at *
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  sat := sat

end VG.Proof.Ed25519.Arm.SignCached

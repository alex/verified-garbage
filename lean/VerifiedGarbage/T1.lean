import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
open VG VG.AArch64 VG.Proof.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.KeyGen
example (p : Spec.MlDsa.Params) (S : Nat) (s : State) (h : (Spec.MlDsa.keyGenContract p AArch64.abi S).pre s) : False := by
  sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at h
  trace_state
  sorry
example (p : Spec.MlDsa.Params) (S : Nat) (s s2 : State) (h : (Spec.MlDsa.keyGenContract p AArch64.abi S).pub s s2) : False := by
  sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at h
  trace_state
  sorry
example (p : Spec.MlDsa.Params) (S : Nat) (s s2 : State) : (Spec.MlDsa.keyGenContract p AArch64.abi S).post s s2 := by
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
  trace_state
  sorry

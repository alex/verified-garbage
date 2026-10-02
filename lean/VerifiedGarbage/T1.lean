import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64 VG.Spec.MlDsa
example {p : Params} {s : State} (h : (signMessageContract p AArch64.abi 16).pre s) : False := by
  sig_pre [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  trace_state
  sorry
example {p : Params} {s₁ s₂ : State} (h : (signMessageContract p AArch64.abi 16).pub s₁ s₂) : False := by
  sig_pub [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  trace_state
  sorry
example {p : Params} {s : State} (h : (signContract p AArch64.abi 16).pre s) : False := by
  sig_pre [signContract, signSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  trace_state
  sorry
example {p : Params} {s₁ s₂ : State} (h : (signContract p AArch64.abi 16).pub s₁ s₂) : False := by
  sig_pub [signContract, signSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  trace_state
  sorry
example {p : Params} {s s' : State} (h : (signContract p AArch64.abi 16).post s s') : False := by
  sig_reduce [signContract, signSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  trace_state
  sorry
end VG.Proof.MlDsa.AArch64.Message

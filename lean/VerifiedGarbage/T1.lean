import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Entry
import VerifiedGarbage.Proof.Framework.Contract
namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64 VG.Spec.MlDsa
example {p : Params} {s : State} (h : (signMessageContract p AArch64.abi 16).pre s) : False := by
  sig_pre [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a1, h⟩ := h
  obtain ⟨a2, h⟩ := h
  obtain ⟨a3, h⟩ := h
  obtain ⟨a4, h⟩ := h
  obtain ⟨a5, h⟩ := h
  obtain ⟨a6, h⟩ := h
  obtain ⟨a7, h⟩ := h
  obtain ⟨a8, h⟩ := h
  obtain ⟨a9, h⟩ := h
  obtain ⟨a10, h⟩ := h
  obtain ⟨a11, h⟩ := h
  obtain ⟨a12, h⟩ := h
  obtain ⟨a13, h⟩ := h
  obtain ⟨a14, h⟩ := h
  obtain ⟨a15, h⟩ := h
  obtain ⟨a16, h⟩ := h
  obtain ⟨a17, h⟩ := h
  obtain ⟨a18, h⟩ := h
  obtain ⟨a19, h⟩ := h
  obtain ⟨a20, h⟩ := h
  sorry
end VG.Proof.MlDsa.AArch64.Message

import VerifiedGarbage.Proof.Argon2.X86_64.FinalOutputArgs
import VerifiedGarbage.Proof.Argon2.X86_64.FinalCall

/-! Final output uses matrix block zero and the original disjoint hash scratch allocation. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  positive : 1 ≤ p.tagLen
  bound : p.tagLen < 2 ^ 32
  reads : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  tagWord : s.mem.readW (off (s.gpr .rbp) 264) 64 = BitVec.ofNat 64 p.tagLen
  input : Covers [⟨ReductionState.matrix s, 1024⟩] (s.rd ++ s.wr)
  outputWrite : Covers [⟨output s, p.tagLen⟩] s.wr
  workWrite : (⟨work s, 16384⟩ : Region) ∈ s.wr
  inputWork : (⟨ReductionState.matrix s, 1024⟩ : Region).Disjoint ⟨work s, 16384⟩
  outputWork : (⟨output s, p.tagLen⟩ : Region).Disjoint ⟨work s, 16384⟩
  stackInput : (below (s.gpr .rsp) 24).Disjoint ⟨ReductionState.matrix s, 1024⟩
  stackOutput : (below (s.gpr .rsp) 24).Disjoint ⟨output s, p.tagLen⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨work s, 16384⟩

theorem Arguments.ready {p : Params} {s t : State} (h : Ready p s) (a : Arguments s t) :
    FinalCall.CallReady p.tagLen t := by
  have sp := a.regs .rsp (by simp [calleeSaved])
  constructor
  · exact h.positive
  · exact h.bound
  · rw [a.input, a.keeps.rd, a.keeps.wr]; exact h.input
  · rw [a.output, a.keeps.wr]; exact h.outputWrite
  · rw [a.work, a.keeps.wr]; exact h.workWrite
  · rw [a.input, a.work]; exact h.inputWork
  · rw [a.output, a.work]; exact h.outputWork
  · rw [a.input, sp]; exact h.stackInput
  · rw [a.output, sp]; exact h.stackOutput
  · rw [a.work, sp]; exact h.stackWork

end VG.Proof.Argon2.X86_64.FinalOutput

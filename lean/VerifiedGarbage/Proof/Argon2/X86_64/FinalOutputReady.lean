import VerifiedGarbage.Proof.Argon2.X86_64.FinalCall
import VerifiedGarbage.Impl.Argon2.X86_64.FinalOutput
import VerifiedGarbage.Proof.Argon2.X86_64.ReductionLoopState

/-! Merged from `Proof.Argon2.X86_64.FinalOutputArgs`. -/
section
/-! Load the public final-call pointers and tag length from the enclosing frame. -/

namespace VG.Proof.Argon2.X86_64.FinalOutput

open VG VG.X86_64 VG.Spec.Argon2

def output (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 256) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

def changed : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8]

structure Arguments (s t : State) : Prop where
  input : t.gpr .rdi = ReductionState.matrix s
  inputLength : t.gpr .rsi = 1024
  output : t.gpr .rdx = output s
  outputLength : t.gpr .rcx = s.mem.readW (off (s.gpr .rbp) 264) 64
  work : t.gpr .r8 = work s
  keeps : Divide.Keeps changed s t

theorem args_ok (s : State) (read : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    WP isa (.block Impl.Argon2.X86_64.FinalOutput.args) s (Arguments s) := by
  have input := read 232 (by simp)
  have out := read 256 (by simp)
  have len := read 264 (by simp)
  have scratch := read 248 (by simp)
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.FinalOutput.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    input, out, len, scratch, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem Arguments.regs {s t : State} (h : Arguments s t) (r : Reg) (hr : r ∈ calleeSaved) : t.gpr r = s.gpr r := by
  have unchanged : r ∉ changed := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.keeps.regs r unchanged

end VG.Proof.Argon2.X86_64.FinalOutput
end

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

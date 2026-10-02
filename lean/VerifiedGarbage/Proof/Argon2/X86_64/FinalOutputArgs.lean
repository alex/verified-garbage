import VerifiedGarbage.Impl.Argon2.X86_64.FinalOutput
import VerifiedGarbage.Proof.Argon2.X86_64.ReductionLoopState

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

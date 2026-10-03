import VerifiedGarbage.Impl.Argon2.AArch64.FinalOutput
import VerifiedGarbage.Proof.Argon2.AArch64.ReductionLoopState

/-! Load the public final-call pointers and tag length from the enclosing frame. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2

def output (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 256) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

def changed : List Reg := [.x0, .x1, .x2, .x3, .x4]

structure Arguments (s t : State) : Prop where
  input : t.gpr .x0 = ReductionState.matrix s
  inputLength : t.gpr .x1 = 1024
  output : t.gpr .x2 = output s
  outputLength : t.gpr .x3 = s.mem.readW (off (s.gpr .x19) 264) 64
  work : t.gpr .x4 = work s
  keeps : Divide.Keeps changed s t

theorem args_ok (s : State) (read : ∀ d ∈ [232, 256, 264, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    WP isa (.block Impl.Argon2.AArch64.FinalOutput.args) s (Arguments s) := by
  have input := read 232 (by simp)
  have out := read 256 (by simp)
  have len := read 264 (by simp)
  have scratch := read 248 (by simp)
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.FinalOutput.args,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.imm,
    show 1024 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load, addr, Size.bytes, Size.bits,
    show 232 % 8 = 0 ∧ 232 < 4096 * 8 from by decide,
    show 256 % 8 = 0 ∧ 256 < 4096 * 8 from by decide,
    show 264 % 8 = 0 ∧ 264 < 4096 * 8 from by decide,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide, and_self,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1024#16).setWidth 64 = 1024#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    input, out, len, scratch, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · constructor
    · intro r hr
      simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
    all_goals rfl

theorem Arguments.regs {s t : State} (h : Arguments s t) (r : Reg) (hr : r ∈ FillCompress.loopRegs) : t.gpr r = s.gpr r := by
  have unchanged : r ∉ changed := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.keeps.regs r unchanged

end VG.Proof.Argon2.AArch64.FinalOutput

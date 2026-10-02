import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceMap
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep

/-! Register preparation for the reference-index stages. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem pass_ea (s : State) : s.ea { base := .rbp } = s.gpr .rbp := by
  change s.gpr .rbp + 0#64 = s.gpr .rbp
  exact BitVec.add_zero _

theorem loadPass_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp) 8) :
    WP isa (.block loadPass) s fun t =>
      t.gpr .r9 = s.mem.readW (s.gpr .rbp) 64 ∧ Divide.Keeps [.r9] s t := by
  apply WP.of_runBlock
  simp only [loadPass, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    pass_ea, State.load64, read, ite_true, Option.map_some, RegUpd.gpr_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem laneArgs_ok (s : State) : WP isa (.block laneArgs) s fun t =>
    t.gpr .rdi = s.gpr .r8 ∧ t.gpr .rsi = s.gpr .rbx ∧
    Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [laneArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

theorem relativeArgs_ok (s : State) : WP isa (.block relativeArgs) s fun t =>
    t.gpr .r9 = s.gpr .rdi ∧ t.gpr .rdi = s.gpr .r11 ∧ t.gpr .rsi = s.gpr .r8 ∧
    Divide.Keeps [.r9, .rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [relativeArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem wrapArgs_ok (s : State) : WP isa (.block wrapArgs) s fun t =>
    t.gpr .rdi = s.gpr .rax + s.gpr .r10 ∧ t.gpr .rsi = s.gpr .r12 ∧
    Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [wrapArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.ReferenceMap

import VerifiedGarbage.Impl.Argon2.X86_64.FillPointers
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep

/-! Short register-setup steps for the filling pointers. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

theorem saveReference_ok (s : State) : WP isa (.block saveReference) s fun t =>
    t.gpr .rsi = s.gpr .rdi ∧ Divide.Keeps [.rsi] s t := by
  apply WP.of_runBlock
  simp only [saveReference, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem currentArgs_ok (s : State) : WP isa (.block currentArgs) s fun t =>
    t.gpr .rax = s.gpr .rbx ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [currentArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem previousArgs_ok (s : State) : WP isa (.block previousArgs) s fun t =>
    t.gpr .r10 = s.gpr .rax ∧ t.gpr .rcx = s.gpr .rdi ∧ t.gpr .rax = s.gpr .rbx ∧
    Divide.Keeps [.r10, .rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [previousArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem referenceArgs_ok (s : State) : WP isa (.block referenceArgs) s fun t =>
    t.gpr .r11 = s.gpr .rax ∧ t.gpr .rcx = s.gpr .rsi ∧ t.gpr .rax = s.gpr .r9 ∧
    Divide.Keeps [.r11, .rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [referenceArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem finishArgs_ok (s : State) : WP isa (.block finishArgs) s fun t =>
    t.gpr .rsi = s.gpr .rax ∧ t.gpr .rdi = s.gpr .r11 ∧
    Divide.Keeps [.rsi, .rdi] s t := by
  apply WP.of_runBlock
  simp only [finishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.FillPointers

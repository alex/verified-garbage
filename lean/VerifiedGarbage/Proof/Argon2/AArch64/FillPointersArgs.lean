import VerifiedGarbage.Impl.Argon2.AArch64.FillPointers
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep

/-! Short register-setup steps for the filling pointers. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers
open VG.Impl.Argon2.AArch64

theorem saveReference_ok (s : State) : WP isa (.block saveReference) s fun t =>
    t.gpr .x1 = s.gpr .x0 ∧ Divide.Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [saveReference, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact by simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem currentArgs_ok (s : State) : WP isa (.block currentArgs) s fun t =>
    t.gpr .x8 = s.gpr .x24 ∧ Divide.Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [currentArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact by simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem previousArgs_ok (s : State) : WP isa (.block previousArgs) s fun t =>
    t.gpr .x6 = s.gpr .x8 ∧ t.gpr .x3 = s.gpr .x0 ∧ t.gpr .x8 = s.gpr .x24 ∧
    Divide.Keeps [.x6, .x3, .x8] s t := by
  apply WP.of_runBlock
  simp only [previousArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem referenceArgs_ok (s : State) : WP isa (.block referenceArgs) s fun t =>
    t.gpr .x7 = s.gpr .x8 ∧ t.gpr .x3 = s.gpr .x1 ∧ t.gpr .x8 = s.gpr .x5 ∧
    Divide.Keeps [.x7, .x3, .x8] s t := by
  apply WP.of_runBlock
  simp only [referenceArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem finishArgs_ok (s : State) : WP isa (.block finishArgs) s fun t =>
    t.gpr .x1 = s.gpr .x8 ∧ t.gpr .x0 = s.gpr .x7 ∧
    Divide.Keeps [.x1, .x0] s t := by
  apply WP.of_runBlock
  simp only [finishArgs, Instructions.mov, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.FillPointers

import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceMap
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep

/-! Register preparation for the reference-index stages. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap
open VG.Impl.Argon2.AArch64

theorem loadPass_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .x19) 8) :
    WP isa (.block loadPass) s fun t =>
      t.gpr .x5 = s.mem.readW (s.gpr .x19) 64 ∧ Divide.Keeps [.x5] s t := by
  apply WP.of_runBlock
  simp only [loadPass, Instructions.load, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, Size.bits, show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide,
    BitVec.add_zero, State.load, read, and_self, ite_true, Option.map_some, Option.bind_some,
    RegUpd.gpr_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem laneArgs_ok (s : State) : WP isa (.block laneArgs) s fun t =>
    t.gpr .x0 = s.gpr .x4 ∧ t.gpr .x1 = s.gpr .x24 ∧
    Divide.Keeps [.x0, .x1] s t := by
  apply WP.of_runBlock
  simp only [laneArgs, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem relativeArgs_ok (s : State) : WP isa (.block relativeArgs) s fun t =>
    t.gpr .x5 = s.gpr .x0 ∧ t.gpr .x0 = s.gpr .x7 ∧ t.gpr .x1 = s.gpr .x4 ∧
    Divide.Keeps [.x5, .x0, .x1] s t := by
  apply WP.of_runBlock
  simp only [relativeArgs, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem wrapArgs_ok (s : State) : WP isa (.block wrapArgs) s fun t =>
    t.gpr .x0 = s.gpr .x8 + s.gpr .x6 ∧ t.gpr .x1 = s.gpr .x20 ∧
    Divide.Keeps [.x0, .x1, .x15] s t := by
  apply WP.of_runBlock
  simp only [wrapArgs, Instructions.mov, Instructions.add, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.ReferenceMap

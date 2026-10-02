import VerifiedGarbage.Impl.Argon2.AArch64.FirstLane
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep

/-! The first reference window stays in the current lane. -/

namespace VG.Proof.Argon2.AArch64.FirstLane

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FirstLane
open VG.Impl.Argon2.AArch64

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    t.gpr .x15 = s.gpr .x5 ||| s.gpr .x22 ∧ Divide.Keeps [.x8, .x15] s t := by
  apply WP.of_runBlock
  simp only [test, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.logic, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    BitVec.setWidth_eq, show 0 < 4096 from by decide, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem current_ok (s : State) : WP isa (.block current) s fun t =>
    t.gpr .x4 = s.gpr .x24 ∧ Divide.Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [current, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, ite_true, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x4 = (if s.gpr .x5 = 0 ∧ s.gpr .x22 = 0 then s.gpr .x24 else s.gpr .x4) ∧
    Divide.Keeps [.x8, .x4, .x15] s t := by
  unfold code
  refine WP.seq ((test_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .x5 = 0 ∧ s.gpr .x22 = 0))
    (by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact BitVec.or_eq_zero_iff) ?_ ?_
  · intro h
    have position := of_decide_eq_true h
    refine (current_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [position, and_self, ite_true, keeps.regs .x24 (by decide)] using out
  · intro h
    have position := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, keeps.mono (by decide)⟩
    simp only [position, ite_false]
    exact keeps.regs .x4 (by decide)

end VG.Proof.Argon2.AArch64.FirstLane

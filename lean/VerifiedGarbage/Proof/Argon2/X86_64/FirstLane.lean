import VerifiedGarbage.Impl.Argon2.X86_64.FirstLane
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep

/-! The first reference window stays in the current lane. -/

namespace VG.Proof.Argon2.X86_64.FirstLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FirstLane

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    t.zf = decide (s.gpr .r9 = 0 ∧ s.gpr .r14 = 0) ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [test, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.zf_setReg, RegUpd.zf_arithFlags,
    reduceCtorEq, ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    change (s.gpr .r9 ||| s.gpr .r14) = 0#64 ↔ _
    exact BitVec.or_eq_zero_iff
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

theorem current_ok (s : State) : WP isa (.block current) s fun t =>
    t.gpr .r8 = s.gpr .rbx ∧ Divide.Keeps [.r8] s t := by
  apply WP.of_runBlock
  simp only [current, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .r8 = (if s.gpr .r9 = 0 ∧ s.gpr .r14 = 0 then s.gpr .rbx else s.gpr .r8) ∧
    Divide.Keeps [.rax, .r8] s t := by
  unfold code
  refine WP.seq ((test_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .r9 = 0 ∧ s.gpr .r14 = 0))
    (by simp only [eval, flag]) ?_ ?_
  · intro h
    have position := of_decide_eq_true h
    refine (current_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [position, and_self, ite_true, keeps.regs .rbx (by decide)] using out
  · intro h
    have position := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, keeps.mono (by decide)⟩
    simp only [position, ite_false]
    exact keeps.regs .r8 (by decide)

end VG.Proof.Argon2.X86_64.FirstLane

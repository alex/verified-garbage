import VerifiedGarbage.Impl.Argon2.X86_64.CountCandidates
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep

/-! # Candidate window arithmetic before selecting the reference lane -/

namespace VG.Proof.Argon2.X86_64.CountCandidates

open VG VG.X86_64 VG.Impl.Argon2.X86_64.CountCandidates

structure Candidates (s t : State) (base : Addr) : Prop where
  same : t.gpr .rdx = base + s.gpr .r15 - 1
  other : t.gpr .rcx = base
  keeps : Divide.Keeps [.rax, .rdx, .rcx] s t

theorem first_ok (s : State) : WP isa (.block first) s
    (Candidates s · (s.gpr .r13 * s.gpr .r14)) := by
  apply WP.of_runBlock
  simp only [first, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execMul, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl]
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem later_ok (s : State) : WP isa (.block later) s
    (Candidates s · (s.gpr .r12 - s.gpr .r13)) := by
  apply WP.of_runBlock
  simp only [later, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl]
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

structure Adjusted (s t : State) : Prop where
  count : t.gpr .rcx = s.gpr .rcx + Divide.mask (decide ((s.gpr .r15).toNat < 1))
  keeps : Divide.Keeps [.r8, .r9, .rcx] s t

theorem adjust_ok (s : State) : WP isa (.block adjust) s (Adjusted s) := by
  apply WP.of_runBlock
  simp only [adjust, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', Divide.sbb_mask,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show (1 : Addr).toNat = 1 from rfl]
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem compare_ok (s : State) : WP isa (.block [.alu .cmp .r9 (.imm 0)]) s
    fun t => t.zf = decide (s.gpr .r9 = 0) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.zf_arithFlags,
    show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change (s.gpr .r9 - (0 : Addr) == (0 : Addr)) = decide (s.gpr .r9 = 0)
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    change s.gpr .r9 - 0#64 = 0#64 ↔ s.gpr .r9 = 0#64
    rw [BitVec.sub_zero]
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

def base (s : State) : Addr :=
  if s.gpr .r9 = 0 then s.gpr .r13 * s.gpr .r14 else s.gpr .r12 - s.gpr .r13

def changed : List Reg := [.rax, .rdx, .rcx, .r8, .r9]

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .rdx = base s + s.gpr .r15 - 1 ∧
    t.gpr .rcx = base s + Divide.mask (decide ((s.gpr .r15).toNat < 1)) ∧
    Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((compare_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  have branches : WP isa (.ite .e (.block first) (.block later)) a
      (Candidates s · (base s)) := by
    refine WP.ite (decide (s.gpr .r9 = 0)) (by simp only [eval, flag]) ?_ ?_
    · intro h
      have zero : s.gpr .r9 = 0 := of_decide_eq_true h
      refine (first_ok a).mono ?_
      intro b hb
      refine ⟨?_, ?_, keeps.mono (by simp) |>.trans hb.keeps⟩
      · simpa only [base, zero, ite_true, keeps.regs .r13 (by simp),
          keeps.regs .r14 (by simp), keeps.regs .r15 (by simp)] using hb.same
      · simpa only [base, zero, ite_true, keeps.regs .r13 (by simp),
          keeps.regs .r14 (by simp)] using hb.other
    · intro h
      have nonzero : s.gpr .r9 ≠ 0 := of_decide_eq_false h
      refine (later_ok a).mono ?_
      intro b hb
      refine ⟨?_, ?_, keeps.mono (by simp) |>.trans hb.keeps⟩
      · simpa only [base, nonzero, ite_false, keeps.regs .r12 (by simp),
          keeps.regs .r13 (by simp), keeps.regs .r15 (by simp)] using hb.same
      · simpa only [base, nonzero, ite_false, keeps.regs .r12 (by simp),
          keeps.regs .r13 (by simp)] using hb.other
  refine WP.seq (branches.mono ?_)
  intro b hb
  refine (adjust_ok b).mono ?_
  intro t ht
  refine ⟨?_, ?_, (hb.keeps.mono (by decide)).trans (ht.keeps.mono (by decide))⟩
  · exact (ht.keeps.regs .rdx (by decide)).trans hb.same
  · rw [ht.count, hb.other, hb.keeps.regs .r15 (by decide)]

end VG.Proof.Argon2.X86_64.CountCandidates

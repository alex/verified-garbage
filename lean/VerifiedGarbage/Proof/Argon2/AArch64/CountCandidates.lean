import VerifiedGarbage.Impl.Argon2.AArch64.CountCandidates
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep

/-! # Candidate window arithmetic before selecting the reference lane -/

namespace VG.Proof.Argon2.AArch64.CountCandidates

open VG VG.AArch64 VG.Impl.Argon2.AArch64.CountCandidates
open VG.Impl.Argon2.AArch64

structure Candidates (s t : State) (base : Addr) : Prop where
  same : t.gpr .x2 = base + s.gpr .x23 - 1
  other : t.gpr .x3 = base
  keeps : Divide.Keeps [.x8, .x2, .x3, .x12, .x13, .x14, .x15] s t

theorem first_ok (s : State) : WP isa (.block first) s
    (Candidates s · (s.gpr .x21 * s.gpr .x22)) := by
  apply WP.of_runBlock
  simp only [first, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.mul, Instructions.add, Instructions.subi,
    Instructions.sub, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', Bool.toNat_true, sub_value]
  constructor
  · simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, Size.bits,
      BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, sub_value,
      Bool.toNat_true]
    rfl
  · simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, Size.bits,
      BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, sub_value,
      Bool.toNat_true]
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

theorem later_ok (s : State) : WP isa (.block later) s
    (Candidates s · (s.gpr .x20 - s.gpr .x21)) := by
  apply WP.of_runBlock
  simp only [later, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.add, Instructions.subi,
    Instructions.sub, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', Bool.toNat_true, sub_value]
  constructor
  · simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, Size.bits,
      BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, sub_value,
      Bool.toNat_true]
    rfl
  · simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, Size.bits,
      BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, sub_value,
      Bool.toNat_true]
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

structure Adjusted (s t : State) : Prop where
  count : t.gpr .x3 = s.gpr .x3 + Divide.mask (decide ((s.gpr .x23).toNat < 1))
  keeps : Divide.Keeps [.x4, .x5, .x3, .x12, .x15] s t

theorem adjust_ok (s : State) : WP isa (.block adjust) s (Adjusted s) := by
  apply WP.of_runBlock
  simp only [adjust, Instructions.sbb, RegUpd.c_write, RegUpd.c_addWithCarry,
    borrow_mask, sub_carry, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.add, Instructions.subi,
    Instructions.sub, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', Bool.toNat_true, sub_value]
  have hm : (if decide (1 ≤ (s.gpr .x23).toNat) then 0 else -1) =
      Divide.mask (decide ((s.gpr .x23).toNat < 1)) := by
    by_cases h : (s.gpr .x23).toNat < 1
    · simp only [Divide.mask, h, Nat.not_le_of_gt h, decide_false, decide_true,
        Bool.false_eq_true, ite_false, ite_true]
    · simp only [Divide.mask, h, Nat.le_of_not_gt h, decide_false, decide_true,
        Bool.false_eq_true, ite_false, ite_true]
  simp only [show (1#64).toNat = 1 from rfl, hm]
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem compare_ok (s : State) : WP isa (.block ([Instructions.comparei .x5 0].flatten)) s
    fun t => t.gpr .x15 = s.gpr .x5 ∧ Divide.Keeps [.x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.comparei, Instructions.compare, Instructions.imm,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    reduceCtorEq, ite_true, ite_false, show 0 < 65536 from by decide,
    Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, Bool.toNat_true, sub_value,
    show (BitVec.ofNat 16 0).setWidth 64 = 0#64 from rfl, BitVec.sub_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

def base (s : State) : Addr :=
  if s.gpr .x5 = 0 then s.gpr .x21 * s.gpr .x22 else s.gpr .x20 - s.gpr .x21

def changed : List Reg := [.x8, .x2, .x3, .x4, .x5, .x12, .x13, .x14, .x15]

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x2 = base s + s.gpr .x23 - 1 ∧
    t.gpr .x3 = base s + Divide.mask (decide ((s.gpr .x23).toNat < 1)) ∧
    Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((compare_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  have branches : WP isa (.ite (.zero .x .x15) (.block first) (.block later)) a
      (Candidates s · (base s)) := by
    refine WP.ite (decide (s.gpr .x5 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
    · intro h
      have zero : s.gpr .x5 = 0 := of_decide_eq_true h
      refine (first_ok a).mono ?_
      intro b hb
      refine ⟨?_, ?_, keeps.mono (by decide) |>.trans hb.keeps⟩
      · simpa only [base, zero, ite_true, keeps.regs .x21 (by simp),
          keeps.regs .x22 (by simp), keeps.regs .x23 (by simp)] using hb.same
      · simpa only [base, zero, ite_true, keeps.regs .x21 (by simp),
          keeps.regs .x22 (by simp)] using hb.other
    · intro h
      have nonzero : s.gpr .x5 ≠ 0 := of_decide_eq_false h
      refine (later_ok a).mono ?_
      intro b hb
      refine ⟨?_, ?_, keeps.mono (by decide) |>.trans hb.keeps⟩
      · simpa only [base, nonzero, ite_false, keeps.regs .x20 (by simp),
          keeps.regs .x21 (by simp), keeps.regs .x23 (by simp)] using hb.same
      · simpa only [base, nonzero, ite_false, keeps.regs .x20 (by simp),
          keeps.regs .x21 (by simp)] using hb.other
  refine WP.seq (branches.mono ?_)
  intro b hb
  refine (adjust_ok b).mono ?_
  intro t ht
  refine ⟨?_, ?_, (hb.keeps.mono (by decide)).trans (ht.keeps.mono (by decide))⟩
  · exact (ht.keeps.regs .x2 (by decide)).trans hb.same
  · rw [ht.count, hb.other, hb.keeps.regs .x23 (by decide)]

end VG.Proof.Argon2.AArch64.CountCandidates

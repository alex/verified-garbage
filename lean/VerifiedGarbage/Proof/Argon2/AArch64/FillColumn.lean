import VerifiedGarbage.Impl.Argon2.AArch64.FillColumn
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-! Current-column arithmetic and the cyclic predecessor, preserving the
matrix, enclosing loop registers and the stack pointer. -/

namespace VG.Proof.Argon2.AArch64.FillColumn

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillColumn
open VG.Impl.Argon2.AArch64

theorem current_ok (s : State) : WP isa (.block current) s fun t =>
    t.gpr .x3 = s.gpr .x22 * s.gpr .x21 + s.gpr .x23 ∧
    Divide.Keeps [.x8, .x2, .x3, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [current, Instructions.mov, Instructions.mul, Instructions.add,
    Instructions.mark, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left' ]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

theorem compare_ok (s : State) : WP isa (.block [Instructions.comparei .x3 0].flatten) s
    fun t => t.gpr .x15 = s.gpr .x3 ∧ Divide.Keeps [.x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.comparei, Instructions.compare, Instructions.imm,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    reduceCtorEq, ite_true, ite_false, show 0 < 65536 from by decide,
    Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, Bool.toNat_true, sub_value,
    show (BitVec.ofNat 16 0).setWidth 64 = 0#64 from rfl,
    BitVec.sub_zero, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem move_ok (s : State) (r : Reg) : WP isa (.block [Instructions.mov .x0 r].flatten) s
    fun t => t.gpr .x0 = s.gpr r ∧ Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.mov, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    ite_true, Option.some.injEq, exists_eq_left' ]
  refine ⟨trivial, ?_⟩
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, ite_false]
  all_goals rfl

theorem decrement_ok (s : State) : WP isa (.block [Instructions.subi .x0 1].flatten) s
    fun t => t.gpr .x0 = s.gpr .x0 - 1 ∧ Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.subi, Instructions.sub, Instructions.imm, Instructions.mark, Instructions.mov,
    RegUpd.gpr_addWithCarry, show 1 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    Bool.toNat_true, sub_value,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left' ]
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem previous_ok (s : State) : WP isa previous s fun t =>
    t.gpr .x0 = (if s.gpr .x3 = 0 then s.gpr .x20 else s.gpr .x3) - 1 ∧
    Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s t := by
  unfold previous
  refine WP.seq ((compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have selected : WP isa select a fun b =>
      b.gpr .x0 = (if s.gpr .x3 = 0 then s.gpr .x20 else s.gpr .x3) ∧
      Divide.Keeps [.x0, .x12, .x13, .x14, .x15] s b := by
    unfold select
    refine WP.ite (decide (s.gpr .x3 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
    · intro h
      have zero := of_decide_eq_true h
      refine (move_ok a .x20).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .x20 (by decide), ite_eq_left zero],
        (ka.mono (by decide)).trans kb⟩
    · intro h
      have nonzero := of_decide_eq_false h
      refine (move_ok a .x3).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .x3 (by decide), ite_eq_right nonzero],
        (ka.mono (by decide)).trans kb⟩
  refine WP.seq (selected.mono ?_)
  rintro b ⟨value, kb⟩
  refine (decrement_ok b).mono ?_
  rintro t ⟨result, kt⟩
  exact ⟨by rw [result, value], kb.trans kt⟩

theorem code_ok (s : State) : WP isa code s fun t =>
    let column := s.gpr .x22 * s.gpr .x21 + s.gpr .x23
    t.gpr .x3 = column ∧
    t.gpr .x0 = (if column = 0 then s.gpr .x20 else column) - 1 ∧
    Divide.Keeps [.x8, .x2, .x3, .x0, .x12, .x13, .x14, .x15] s t := by
  unfold code
  refine WP.seq ((current_ok s).mono ?_)
  rintro a ⟨column, ka⟩
  refine (previous_ok a).mono ?_
  rintro t ⟨previous, kt⟩
  refine ⟨(kt.regs .x3 (by decide)).trans column, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [previous, column, ka.regs .x20 (by decide)]

theorem previous_nat (column q : Nat) (positive : 0 < q) (bound : column < q) :
    (if column = 0 then q else column) - 1 = (column + q - 1) % q := by
  by_cases zero : column = 0
  · simp only [zero, ite_true, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (by omega : q - 1 < q)).symm
  · simp only [zero, ite_false]
    have sub : column + q - 1 - q = column - 1 := by omega
    rw [Nat.mod_eq_sub_mod (by omega : q ≤ column + q - 1), sub,
      Nat.mod_eq_of_lt (by omega : column - 1 < q)]

theorem previous_word_nat (column q : Nat) (positive : 0 < q) (qBound : q < 2 ^ 64)
    (bound : column < q) :
    (if BitVec.ofNat 64 column = 0#64 then BitVec.ofNat 64 q else BitVec.ofNat 64 column) - 1 =
      BitVec.ofNat 64 ((column + q - 1) % q) := by
  have zero : BitVec.ofNat 64 column = 0#64 ↔
      column = 0 := by
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bound qBound)] at hn
      exact hn
    · intro h; rw [h]
  simp only [zero]
  by_cases h : column = 0
  · simp only [h, ite_true]
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat positive, Nat.zero_add, Nat.mod_eq_of_lt (by omega : q - 1 < q)]
  · simp only [h, ite_false]
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 1 ≤ column),
      ← previous_nat _ q positive bound, ite_eq_right h]

theorem code_nat_ok (s : State) (slice segment index q : Nat)
    (hs : s.gpr .x22 = BitVec.ofNat 64 slice)
    (hg : s.gpr .x21 = BitVec.ofNat 64 segment)
    (hi : s.gpr .x23 = BitVec.ofNat 64 index)
    (hq : s.gpr .x20 = BitVec.ofNat 64 q)
    (positive : 0 < q) (qBound : q < 2 ^ 64)
    (bound : slice * segment + index < q) :
    WP isa code s fun t =>
      t.gpr .x3 = BitVec.ofNat 64 (slice * segment + index) ∧
      t.gpr .x0 = BitVec.ofNat 64 ((slice * segment + index + q - 1) % q) ∧
      Divide.Keeps [.x8, .x2, .x3, .x0, .x12, .x13, .x14, .x15] s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨column, previous, keeps⟩
  have word : s.gpr .x22 * s.gpr .x21 + s.gpr .x23 =
      BitVec.ofNat 64 (slice * segment + index) := by
    rw [hs, hg, hi, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  refine ⟨column.trans word, ?_, keeps⟩
  rw [previous, word, hq]
  exact previous_word_nat _ q positive qBound bound

end VG.Proof.Argon2.AArch64.FillColumn

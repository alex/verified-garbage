import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMap
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompress
import VerifiedGarbage.Impl.Argon2.AArch64.FillKernel
import VerifiedGarbage.Proof.Argon2.AArch64.Memory
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapState
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Argon2.AArch64.BlockAddress
import VerifiedGarbage.Impl.Argon2.AArch64.FillColumn
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Impl.Argon2.AArch64.FillPointers

/-! Merged from `Proof.Argon2.AArch64.FillPointersNat`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillPointersArgs`. -/
section
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
end

/-! Merged from `Proof.Argon2.AArch64.FillPointers`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillColumn`. -/
section
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
end

/-! Compose the matrix addresses while retaining the enclosing loop position. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers
open VG.Impl.Argon2.AArch64

def address (base lane column q : Addr) : Addr := (lane * q + column) * 1024 + base

def column (s : State) : Addr := s.gpr .x22 * s.gpr .x21 + s.gpr .x23

def predecessor (s : State) : Addr :=
  (if column s = 0 then s.gpr .x20 else column s) - 1

def changed : List Reg := [.x8, .x2, .x3, .x0, .x1, .x6, .x7, .x12, .x13, .x14, .x15]

theorem current_ok (s : State) : WP isa current s fun t =>
    t.gpr .x8 = address (s.gpr .x4) (s.gpr .x24) (s.gpr .x3) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  unfold current
  refine WP.seq ((currentArgs_ok s).mono ?_)
  rintro a ⟨lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨?_, (ka.mono (by decide)).trans kt⟩
  rw [pointer, lane, ka.regs .x20 (by decide), ka.regs .x3 (by decide), ka.regs .x4 (by decide), address]

theorem previous_ok (s : State) : WP isa previous s fun t =>
    t.gpr .x6 = s.gpr .x8 ∧
    t.gpr .x8 = address (s.gpr .x4) (s.gpr .x24) (s.gpr .x0) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x3, .x6, .x15] s t := by
  unfold previous
  refine WP.seq ((previousArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .x6 (by decide)).trans saved, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointer, lane, col, ka.regs .x20 (by decide), ka.regs .x4 (by decide), address]

theorem reference_ok (s : State) : WP isa reference s fun t =>
    t.gpr .x7 = s.gpr .x8 ∧
    t.gpr .x8 = address (s.gpr .x4) (s.gpr .x5) (s.gpr .x1) (s.gpr .x20) ∧
    Divide.Keeps [.x8, .x2, .x3, .x7, .x15] s t := by
  unfold reference
  refine WP.seq ((referenceArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .x7 (by decide)).trans saved, ?_,
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointer, lane, col, ka.regs .x20 (by decide), ka.regs .x4 (by decide), address]

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x6 = address (s.gpr .x4) (s.gpr .x24) (column s) (s.gpr .x20) ∧
    t.gpr .x0 = address (s.gpr .x4) (s.gpr .x24) (predecessor s) (s.gpr .x20) ∧
    t.gpr .x1 = address (s.gpr .x4) (s.gpr .x5) (s.gpr .x0) (s.gpr .x20) ∧
    Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((saveReference_ok s).mono ?_)
  rintro a ⟨refColumn, ka⟩
  refine WP.seq ((FillColumn.code_ok a).mono ?_)
  rintro b ⟨curColumn, prevColumn, kb⟩
  refine WP.seq ((current_ok b).mono ?_)
  rintro c ⟨curPointer, kc⟩
  refine WP.seq ((previous_ok c).mono ?_)
  rintro d ⟨savedCurrent, prevPointer, kd⟩
  refine WP.seq ((reference_ok d).mono ?_)
  rintro e ⟨savedPrevious, refPointer, ke⟩
  refine (finishArgs_ok e).mono ?_
  rintro t ⟨referenceResult, previousResult, kt⟩
  have coords : column a = column s := by
    unfold column
    rw [ka.regs .x22 (by decide), ka.regs .x21 (by decide), ka.regs .x23 (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kt.regs .x6 (by decide), ke.regs .x6 (by decide), savedCurrent, curPointer,
      kb.regs .x4 (by decide), ka.regs .x4 (by decide), kb.regs .x24 (by decide),
      ka.regs .x24 (by decide), kb.regs .x20 (by decide), ka.regs .x20 (by decide), curColumn]
    exact congrArg (fun col => address (s.gpr .x4) (s.gpr .x24) col (s.gpr .x20)) coords
  · rw [previousResult, savedPrevious, prevPointer, kc.regs .x4 (by decide),
      kc.regs .x24 (by decide), kc.regs .x0 (by decide), kc.regs .x20 (by decide),
      kb.regs .x4 (by decide), ka.regs .x4 (by decide), kb.regs .x24 (by decide),
      ka.regs .x24 (by decide), kb.regs .x20 (by decide), ka.regs .x20 (by decide), prevColumn]
    change address _ _ ((if column a = 0 then a.gpr .x20 else column a) - 1) _ = _
    rw [coords, ka.regs .x20 (by decide), predecessor]
  · rw [referenceResult, refPointer, kd.regs .x4 (by decide), kd.regs .x5 (by decide),
      kd.regs .x1 (by decide), kd.regs .x20 (by decide), kc.regs .x4 (by decide),
      kc.regs .x5 (by decide), kc.regs .x1 (by decide), kc.regs .x20 (by decide),
      kb.regs .x4 (by decide), kb.regs .x5 (by decide), kb.regs .x1 (by decide),
      kb.regs .x20 (by decide), ka.regs .x4 (by decide), ka.regs .x5 (by decide),
      ka.regs .x20 (by decide), refColumn]
  · exact (((((ka.mono (by simp [changed])).trans (kb.mono (by simp [changed]))).trans
      (kc.mono (by simp [changed]))).trans (kd.mono (by simp [changed]))).trans
      (ke.mono (by simp [changed]))).trans (kt.mono (by simp [changed]))

end VG.Proof.Argon2.AArch64.FillPointers
end

/-! Matrix pointers are the natural-number block offsets in the specification. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers

def cell (base : Addr) (p : Spec.Argon2.Params) (lane column : Nat) : Addr :=
  off base ((lane * p.laneLen + column) * 1024)

theorem address_nat (base : Addr) (lane column q : Nat) :
    address base (BitVec.ofNat 64 lane) (BitVec.ofNat 64 column) (BitVec.ofNat 64 q) =
      off base ((lane * q + column) * 1024) := by
  unfold address off
  change (BitVec.ofNat 64 lane * BitVec.ofNat 64 q + BitVec.ofNat 64 column) *
    BitVec.ofNat 64 1024 + base = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, ← BitVec.ofNat_mul, BitVec.add_comm]

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index refLane refColumn : Nat)
    (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (rl : s.gpr .x5 = BitVec.ofNat 64 refLane)
    (rc : s.gpr .x0 = BitVec.ofNat 64 refColumn) :
    WP isa code s fun t =>
      t.gpr .x6 = cell (s.gpr .x4) p lane (slice * p.segmentLen + index) ∧
      t.gpr .x0 = cell (s.gpr .x4) p lane ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) ∧
      t.gpr .x1 = cell (s.gpr .x4) p refLane refColumn ∧ Divide.Keeps changed s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨current, previous, reference, keeps⟩
  have col : column s = BitVec.ofNat 64 (slice * p.segmentLen + index) := by
    unfold column
    rw [position.slice, position.segmentLength, position.index, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  have prev : predecessor s = BitVec.ofNat 64
      ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) := by
    unfold predecessor
    rw [col, position.laneLength]
    have positive := Proof.Argon2.segmentLen_ge_two p bounds.lanesPositive bounds.memoryMinimum
    have q := Proof.Argon2.laneLen_segments p bounds.lanesPositive
    exact FillColumn.previous_word_nat _ _ (by omega)
      (Nat.lt_trans bounds.laneLength_bound (by decide))
      (Proof.Argon2.column_lt p bounds.lanesPositive bounds.sliceBound bounds.indexBound)
  refine ⟨?_, ?_, ?_, keeps⟩
  · rw [current, position.current, col, position.laneLength, address_nat]; rfl
  · rw [previous, position.current, prev, position.laneLength, address_nat]; rfl
  · rw [reference, rl, rc, position.laneLength, address_nat]; rfl

end VG.Proof.Argon2.AArch64.FillPointers
end

/-! Merged from `Proof.Argon2.AArch64.FillKernelLayout`. -/
section
/-! One allocation invariant covers all matrix cells used by the filling step. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 232) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

structure Layout (p : Params) (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 184, 232, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .x19) 16) 8
  matrixWrite : Covers [⟨matrix s, p.blocks * 1024⟩] s.wr
  workWrite : Covers [⟨work s, 5120⟩] s.wr
  matrixWork : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  matrixFrame : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  matrixStack : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint (below s.sp 8)
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨work s, 5120⟩
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below s.sp 8)
  stackWork : (below s.sp 8).Disjoint ⟨work s, 5120⟩

theorem Layout.of_keeps {p : Params} {s t : State} (h : Layout p s)
    (k : Divide.Keeps ReferenceMap.changed s t) : Layout p t := by
  have bp := k.regs .x19 (by decide)
  have sp := k.sp
  have matrix' : matrix t = matrix s := by unfold matrix; rw [bp, k.mem]
  have work' : work t = work s := by unfold work; rw [bp, k.mem]
  constructor
  · rw [k.rd, k.wr, bp]; exact h.frameRead
  · rw [k.wr, bp]; exact h.frameWrite
  · rw [matrix', k.wr]; exact h.matrixWrite
  · rw [work', k.wr]; exact h.workWrite
  · rw [matrix', work']; exact h.matrixWork
  · rw [matrix', bp]; exact h.matrixFrame
  · rw [matrix', sp]; exact h.matrixStack
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem cell_sub (p : Params) (base : Addr) (positive : 0 < p.lanes) {lane column : Nat}
    (hl : lane < p.lanes) (hc : column < p.laneLen) :
    Region.Sub ⟨FillPointers.cell base p lane column, 1024⟩ ⟨base, p.blocks * 1024⟩ :=
  Offset.sub_base base (Proof.Argon2.cell_bytes p positive hl hc)

theorem Layout.cell_cover {p : Params} {s : State} (h : Layout p s) (positive : 0 < p.lanes)
    {lane column : Nat} (hl : lane < p.lanes) (hc : column < p.laneLen) :
    Covers [⟨FillPointers.cell (matrix s) p lane column, 1024⟩] s.wr := by
  have sub : Covers [⟨FillPointers.cell (matrix s) p lane column, 1024⟩]
      [⟨matrix s, p.blocks * 1024⟩] := Covers.of_sub (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨⟨matrix s, p.blocks * 1024⟩, by simp, (lane * p.laneLen + column) * 1024,
          rfl, Proof.Argon2.cell_bytes p positive hl hc⟩)
  exact fun a n ha => h.matrixWrite a n (sub a n ha)

theorem compress_ready (p : Params) (s : State) (layout : Layout p s)
    (positive : 0 < p.lanes) (leftLane leftColumn rightLane rightColumn destLane destColumn : Nat)
    (ll : leftLane < p.lanes) (lc : leftColumn < p.laneLen)
    (rl : rightLane < p.lanes) (rc : rightColumn < p.laneLen)
    (dl : destLane < p.lanes) (dc : destColumn < p.laneLen)
    (left : s.gpr .x0 = FillPointers.cell (matrix s) p leftLane leftColumn)
    (right : s.gpr .x1 = FillPointers.cell (matrix s) p rightLane rightColumn)
    (dest : s.gpr .x6 = FillPointers.cell (matrix s) p destLane destColumn) : FillCompress.Ready s := by
  have leftSub := cell_sub p (matrix s) positive ll lc
  have rightSub := cell_sub p (matrix s) positive rl rc
  have destSub := cell_sub p (matrix s) positive dl dc
  have read (lane column : Nat) (hl : lane < p.lanes) (hc : column < p.laneLen) :
      Covers [⟨FillPointers.cell (matrix s) p lane column, 1024⟩] (s.rd ++ s.wr) := by
    intro a n ha
    obtain ⟨r, hr, hc⟩ := layout.cell_cover positive hl hc a n ha
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  constructor
  · intro d hd
    exact layout.frameRead d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> simp)
  · exact layout.frameWrite
  · rw [left]; exact read leftLane leftColumn ll lc
  · rw [right]; exact read rightLane rightColumn rl rc
  · rw [dest]; exact layout.cell_cover positive dl dc
  · exact layout.workWrite
  · rw [left]; exact layout.matrixWork.sub_left leftSub
  · rw [right]; exact layout.matrixWork.sub_left rightSub
  · rw [dest]; exact layout.matrixWork.sub_left destSub
  · exact layout.frameWork
  · rw [left]; exact layout.matrixFrame.sub_left leftSub
  · rw [right]; exact layout.matrixFrame.sub_left rightSub
  · rw [dest]; exact layout.matrixFrame.sub_left destSub
  · rw [left]; exact (layout.matrixStack.sub_left leftSub).symm
  · rw [right]; exact (layout.matrixStack.sub_left rightSub).symm
  · exact layout.stackWork
  · rw [dest]; exact layout.matrixStack.sub_left destSub
  · exact layout.frameStack

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Reload frame arguments and compose reference mapping with matrix addresses. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem load_ok (s : State) (r : Reg) (d : Nat) (ha : d % 8 = 0) (hb : d < 32768)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.load r .x19 d].flatten) s fun t =>
      t.gpr r = s.mem.readW (off (s.gpr .x19) d) 64 ∧ Divide.Keeps [r] s t := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
    Instructions.load_ok s r .x19 d ha hb read

structure Ready (p : Params) (pass lane slice index : Nat) (s : State) : Prop where
  layout : Layout p s
  bounds : ReferenceMap.Bounds p pass lane slice index
  position : ReferenceMap.Position p lane slice index s
  passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

structure Mapped (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  selected : t.gpr .x5 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).1
  column : t.gpr .x0 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).2
  original : t.gpr .x7 = s.gpr .x0
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem mapping_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.AArch64.FillKernel.mapping s (Mapped s · p pass lane slice index) := by
  unfold Impl.Argon2.AArch64.FillKernel.mapping Impl.Argon2.AArch64.FillKernel.lanes
  refine WP.seq ((load_ok s .x1 184 (by decide) (by decide) (h.layout.frameRead 184 (by simp))).mono ?_)
  rintro a ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have ready : ReferenceMap.Ready p pass lane slice index a := by
    refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩
    · rw [k.rd, k.wr, k.regs .x19 (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
        using h.layout.frameRead 0 (by simp)
    · rw [k.mem, k.regs .x19 (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord
  refine (ReferenceMap.code_spec_ok a p pass lane slice index ready).mono ?_
  rintro t ⟨lane, column, original, tail⟩
  rw [keeps.regs .x0 (by decide)] at lane column original
  exact ⟨lane, column, original, k.trans tail⟩

structure Pointers (s t : State) (p : Params) (lane slice index refLane refColumn : Nat) : Prop where
  current : t.gpr .x6 = FillPointers.cell (matrix s) p lane (slice * p.segmentLen + index)
  previous : t.gpr .x0 = FillPointers.cell (matrix s) p lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen)
  reference : t.gpr .x1 = FillPointers.cell (matrix s) p refLane refColumn
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem pointers_ok (s : State) (p : Params) (pass lane slice index refLane refColumn : Nat)
    (layout : Layout p s) (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (laneWord : s.gpr .x5 = BitVec.ofNat 64 refLane) (columnWord : s.gpr .x0 = BitVec.ofNat 64 refColumn) :
    WP isa Impl.Argon2.AArch64.FillKernel.pointers s (Pointers s · p lane slice index refLane refColumn) := by
  unfold Impl.Argon2.AArch64.FillKernel.pointers Impl.Argon2.AArch64.FillKernel.matrix
  refine WP.seq ((load_ok s .x4 232 (by decide) (by decide) (layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have lane' : a.gpr .x5 = BitVec.ofNat 64 refLane := (keeps.regs .x5 (by decide)).trans laneWord
  have col' : a.gpr .x0 = BitVec.ofNat 64 refColumn := (keeps.regs .x0 (by decide)).trans columnWord
  refine (FillPointers.code_nat_ok a p pass lane slice index refLane refColumn bounds
    (position.of_keeps k) lane' col').mono ?_
  rintro t ⟨current, previous, reference, tail⟩
  rw [base] at current previous reference
  exact ⟨current, previous, reference, k.trans (tail.mono (by decide))⟩

end VG.Proof.Argon2.AArch64.FillKernel

import VerifiedGarbage.Impl.Argon2.X86_64.FillColumn
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Current-column arithmetic and the cyclic predecessor, preserving the
matrix, enclosing loop registers and MXCSR. -/

namespace VG.Proof.Argon2.X86_64.FillColumn

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillColumn

theorem current_ok (s : State) : WP isa (.block current) s fun t =>
    t.gpr .rcx = s.gpr .r14 * s.gpr .r13 + s.gpr .r15 ∧
    Divide.Keeps [.rax, .rdx, .rcx] s t := by
  apply WP.of_runBlock
  simp only [current, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execMul, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem compare_ok (s : State) : WP isa (.block [.alu .cmp .rcx (.imm 0)]) s
    fun t => t.zf = decide (s.gpr .rcx = 0) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl]
  refine ⟨?_, ?_⟩
  · change (s.gpr .rcx - 0#64 == 0#64) = decide (s.gpr .rcx = 0#64)
    rw [BitVec.sub_zero]
    exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, decide_eq_true_eq])
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

theorem move_ok (s : State) (r : Reg) : WP isa (.block [.mov .rdi (.reg r)]) s
    fun t => t.gpr .rdi = s.gpr r ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ite_eq_right hq
  all_goals rfl

theorem decrement_ok (s : State) : WP isa (.block [.alu .sub .rdi (.imm 1)]) s
    fun t => t.gpr .rdi = s.gpr .rdi - 1 ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem previous_ok (s : State) : WP isa previous s fun t =>
    t.gpr .rdi = (if s.gpr .rcx = 0 then s.gpr .r12 else s.gpr .rcx) - 1 ∧
    Divide.Keeps [.rdi] s t := by
  unfold previous
  refine WP.seq ((compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have selected : WP isa select a fun b =>
      b.gpr .rdi = (if s.gpr .rcx = 0 then s.gpr .r12 else s.gpr .rcx) ∧
      Divide.Keeps [.rdi] s b := by
    unfold select
    refine WP.ite (decide (s.gpr .rcx = 0)) (by simp only [eval, flag]) ?_ ?_
    · intro h
      have zero := of_decide_eq_true h
      refine (move_ok a .r12).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .r12 (by simp), ite_eq_left zero],
        (ka.mono (by simp)).trans kb⟩
    · intro h
      have nonzero := of_decide_eq_false h
      refine (move_ok a .rcx).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .rcx (by simp), ite_eq_right nonzero],
        (ka.mono (by simp)).trans kb⟩
  refine WP.seq (selected.mono ?_)
  rintro b ⟨value, kb⟩
  refine (decrement_ok b).mono ?_
  rintro t ⟨result, kt⟩
  exact ⟨by rw [result, value], kb.trans kt⟩

theorem code_ok (s : State) : WP isa code s fun t =>
    let column := s.gpr .r14 * s.gpr .r13 + s.gpr .r15
    t.gpr .rcx = column ∧
    t.gpr .rdi = (if column = 0 then s.gpr .r12 else column) - 1 ∧
    Divide.Keeps [.rax, .rdx, .rcx, .rdi] s t := by
  unfold code
  refine WP.seq ((current_ok s).mono ?_)
  rintro a ⟨column, ka⟩
  refine (previous_ok a).mono ?_
  rintro t ⟨previous, kt⟩
  refine ⟨(kt.regs .rcx (by decide)).trans column, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [previous, column, ka.regs .r12 (by decide)]

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
    (hs : s.gpr .r14 = BitVec.ofNat 64 slice)
    (hg : s.gpr .r13 = BitVec.ofNat 64 segment)
    (hi : s.gpr .r15 = BitVec.ofNat 64 index)
    (hq : s.gpr .r12 = BitVec.ofNat 64 q)
    (positive : 0 < q) (qBound : q < 2 ^ 64)
    (bound : slice * segment + index < q) :
    WP isa code s fun t =>
      t.gpr .rcx = BitVec.ofNat 64 (slice * segment + index) ∧
      t.gpr .rdi = BitVec.ofNat 64 ((slice * segment + index + q - 1) % q) ∧
      Divide.Keeps [.rax, .rdx, .rcx, .rdi] s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨column, previous, keeps⟩
  have word : s.gpr .r14 * s.gpr .r13 + s.gpr .r15 =
      BitVec.ofNat 64 (slice * segment + index) := by
    rw [hs, hg, hi, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  refine ⟨column.trans word, ?_, keeps⟩
  rw [previous, word, hq]
  exact previous_word_nat _ q positive qBound bound

end VG.Proof.Argon2.X86_64.FillColumn

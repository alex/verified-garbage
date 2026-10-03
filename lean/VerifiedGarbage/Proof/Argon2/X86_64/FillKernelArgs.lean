import VerifiedGarbage.Proof.Argon2.X86_64.FillCompress
import VerifiedGarbage.Impl.Argon2.X86_64.FillKernel
import VerifiedGarbage.Proof.Argon2.X86_64.Memory
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapState
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Argon2.X86_64.BlockAddress
import VerifiedGarbage.Impl.Argon2.X86_64.FillColumn
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Impl.Argon2.X86_64.FillPointers
import VerifiedGarbage.Proof.Argon2.X86_64.Wrap
import VerifiedGarbage.Proof.Argon2.X86_64.Relative
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapLane
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStart

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapWindow`. -/
section
/-! The selected eligible window and its chronological starting column. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Counted (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .rdi = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  current : t.gpr .rsi = BitVec.ofNat 64 lane
  count : t.gpr .r8 = BitVec.ofNat 64 (windowSize p pass lane slice index (s.gpr .rdi))
  start : t.gpr .r10 = BitVec.ofNat 64 (windowStart p pass slice)
  original : t.gpr .r11 = s.gpr .rdi
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem window_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (prepared : Prepared p pass lane slice index s a) :
    WP isa window a (Counted p pass lane slice index s) := by
  have segmentPositive : 0 < p.segmentLen :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2)
      (Proof.Argon2.segmentLen_ge_two p bounds.lanesPositive bounds.memoryMinimum)
  unfold window
  refine WP.seq ((ReferenceStart.code_nat_ok a p pass slice bounds.lanesPositive
    segmentPositive bounds.sliceBound prepared.pass prepared.position.slice
    prepared.position.segmentLength).mono ?_)
  rintro b ⟨startWord, kb⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have pb := prepared.position.of_keeps kb'
  have passB : (b.gpr .r9).toNat = pass := by
    rw [kb.regs .r9 (by decide), prepared.pass]
  have same : decide (b.gpr .rdi = b.gpr .rsi) =
      (chosenLane p pass lane slice (s.gpr .rdi) == lane) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
    rw [kb.regs .rdi (by decide), kb.regs .rsi (by decide), prepared.selected, prepared.current]
    exact word_eq _ _ (bounds.chosenLane_bound64 _) bounds.lane_bound64
  refine (ReferenceCount.code_nat_ok b p pass slice index passB pb.laneLength
    pb.segmentLength pb.slice pb.index bounds.segment_le_lane bounds.index_bound64
    bounds.window_positive.1 bounds.window_positive.2).mono ?_
  rintro t ⟨countWord, kt⟩
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, pb.of_keeps kt', prepared.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .rdi (by decide)).trans ((kb.regs .rdi (by decide)).trans prepared.selected)
  · exact (kt.regs .rsi (by decide)).trans ((kb.regs .rsi (by decide)).trans prepared.current)
  · simpa only [windowSize, same] using countWord
  · exact (kt.regs .r10 (by decide)).trans startWord
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans prepared.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapRelative`. -/
section
/-! Apply the squared J₁ mapping while retaining the lane and window start. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem relativeWord_ok (s : State) (positive : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.X86_64.Relative.code s fun t =>
      t.gpr .rax = BitVec.ofNat 64
        ((s.gpr .rsi).toNat - 1 - (s.gpr .rsi).toNat *
          ((s.gpr .rdi &&& 0xffffffff).toNat * (s.gpr .rdi &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧ Divide.Keeps [.rax, .rdx, .rcx] s t := by
  refine WP.mono_mx (by decide +kernel) (Relative.code_nat_ok s positive bound) ?_
  rintro t ⟨out, other, mem, rd, wr⟩ mx
  refine ⟨out, ⟨?_, mem, rd, wr, mx⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact other r hr.1 hr.2.1 hr.2.2

structure Mapped (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  relative : t.gpr .rax = BitVec.ofNat 64 (relativeValue p pass lane slice index (s.gpr .rdi))
  start : t.gpr .r10 = BitVec.ofNat 64 (windowStart p pass slice)
  original : t.gpr .r11 = s.gpr .rdi
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem relative_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (counted : Counted p pass lane slice index s a) :
    WP isa relative a (Mapped p pass lane slice index s) := by
  unfold relative
  refine WP.seq ((relativeArgs_ok a).mono ?_)
  rintro b ⟨selected, random, count, kb⟩
  have countNat : (b.gpr .rsi).toNat = windowSize p pass lane slice index (s.gpr .rdi) := by
    rw [count, counted.count, word_nat _ (Nat.lt_trans (bounds.windowSize_bound32 _) (by decide))]
  have randomWord : b.gpr .rdi = s.gpr .rdi := random.trans counted.original
  refine (relativeWord_ok b
    (by rw [countNat]; exact bounds.windowSize_positive _)
    (by rw [countNat]; exact bounds.windowSize_bound32 _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, counted.position.of_keeps (kb'.trans kt'),
    counted.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .r9 (by decide)).trans (selected.trans counted.selected)
  · simpa only [relativeValue, countNat, randomWord] using out
  · exact (kt.regs .r10 (by decide)).trans ((kb.regs .r10 (by decide)).trans counted.start)
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans counted.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapFinish`. -/
section
/-! Wrap the selected relative position into the lane's columns. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Result (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  column : t.gpr .rdi = BitVec.ofNat 64
    ((windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi)) % p.laneLen)
  original : t.gpr .r11 = s.gpr .rdi
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem finish_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (mapped : Mapped p pass lane slice index s a) :
    WP isa finish a (Result p pass lane slice index s) := by
  unfold finish
  refine WP.seq ((wrapArgs_ok a).mono ?_)
  rintro b ⟨sum, length, kb⟩
  have sumWord : b.gpr .rdi = BitVec.ofNat 64
      (windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi)) := by
    rw [sum, mapped.relative, mapped.start, ← BitVec.ofNat_add, Nat.add_comm]
  have sumBound : windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi)
      < 2 ^ 64 := by
    have small := bounds.sum_bound (s.gpr .rdi)
    have q := bounds.laneLength_bound
    omega
  have sumNat : (b.gpr .rdi).toNat =
      windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .rdi) := by
    rw [sumWord, word_nat _ sumBound]
  have lengthNat : (b.gpr .rsi).toNat = p.laneLen := by
    rw [length, mapped.position.laneLength,
      word_nat _ (Nat.lt_trans bounds.laneLength_bound (by decide))]
  refine (Wrap.code_nat_ok b (by rw [sumNat, lengthNat]; exact bounds.sum_bound _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, mapped.position.of_keeps (kb'.trans kt'),
    mapped.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .r9 (by decide)).trans ((kb.regs .r9 (by decide)).trans mapped.selected)
  · rw [out, sumNat, lengthNat]
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans mapped.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMap`. -/
section
/-! Complete reference mapping against the reviewed RFC specification. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem code_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa code s (Result p pass lane slice index s) := by
  unfold code
  refine WP.seq ((prepareLanes_ok s p pass lane slice index ready).mono ?_)
  intro a ha
  refine WP.seq ((window_ok s a p pass lane slice index ready.bounds ha).mono ?_)
  intro b hb
  refine WP.seq ((relative_ok s b p pass lane slice index ready.bounds hb).mono ?_)
  intro c hc
  exact finish_ok s c p pass lane slice index ready.bounds hc

theorem spec_lane (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).1 = chosenLane p pass lane slice random := rfl

theorem spec_column (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).2 =
      (windowStart p pass slice + relativeValue p pass lane slice index random) % p.laneLen := rfl

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa code s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).1 ∧
      t.gpr .rdi = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).2 ∧
      t.gpr .r11 = s.gpr .rdi ∧ Divide.Keeps changed s t := by
  refine (code_ok s p pass lane slice index ready).mono ?_
  intro t h
  rw [spec_lane, spec_column]
  exact ⟨h.selected, h.column, h.original, h.keeps⟩

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.FillPointersNat`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillPointersArgs`. -/
section
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
end

/-! Merged from `Proof.Argon2.X86_64.FillPointers`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillColumn`. -/
section
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
end

/-! Compose the matrix addresses while retaining the enclosing loop position. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

def address (base lane column q : Addr) : Addr := (lane * q + column) * 1024 + base

def column (s : State) : Addr := s.gpr .r14 * s.gpr .r13 + s.gpr .r15

def predecessor (s : State) : Addr :=
  (if column s = 0 then s.gpr .r12 else column s) - 1

def changed : List Reg := [.rax, .rdx, .rcx, .rdi, .rsi, .r10, .r11]

theorem current_ok (s : State) : WP isa current s fun t =>
    t.gpr .rax = address (s.gpr .r8) (s.gpr .rbx) (s.gpr .rcx) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx] s t := by
  unfold current
  refine WP.seq ((currentArgs_ok s).mono ?_)
  rintro a ⟨lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨?_, (ka.mono (by simp)).trans kt⟩
  rw [pointer, lane, ka.regs .r12 (by decide), ka.regs .rcx (by decide), ka.regs .r8 (by decide), address]

theorem previous_ok (s : State) : WP isa previous s fun t =>
    t.gpr .r10 = s.gpr .rax ∧
    t.gpr .rax = address (s.gpr .r8) (s.gpr .rbx) (s.gpr .rdi) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx, .rcx, .r10] s t := by
  unfold previous
  refine WP.seq ((previousArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .r10 (by decide)).trans saved, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [pointer, lane, col, ka.regs .r12 (by decide), ka.regs .r8 (by decide), address]

theorem reference_ok (s : State) : WP isa reference s fun t =>
    t.gpr .r11 = s.gpr .rax ∧
    t.gpr .rax = address (s.gpr .r8) (s.gpr .r9) (s.gpr .rsi) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx, .rcx, .r11] s t := by
  unfold reference
  refine WP.seq ((referenceArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .r11 (by decide)).trans saved, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [pointer, lane, col, ka.regs .r12 (by decide), ka.regs .r8 (by decide), address]

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .r10 = address (s.gpr .r8) (s.gpr .rbx) (column s) (s.gpr .r12) ∧
    t.gpr .rdi = address (s.gpr .r8) (s.gpr .rbx) (predecessor s) (s.gpr .r12) ∧
    t.gpr .rsi = address (s.gpr .r8) (s.gpr .r9) (s.gpr .rdi) (s.gpr .r12) ∧
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
    rw [ka.regs .r14 (by decide), ka.regs .r13 (by decide), ka.regs .r15 (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kt.regs .r10 (by decide), ke.regs .r10 (by decide), savedCurrent, curPointer,
      kb.regs .r8 (by decide), ka.regs .r8 (by decide), kb.regs .rbx (by decide),
      ka.regs .rbx (by decide), kb.regs .r12 (by decide), ka.regs .r12 (by decide), curColumn]
    exact congrArg (fun col => address (s.gpr .r8) (s.gpr .rbx) col (s.gpr .r12)) coords
  · rw [previousResult, savedPrevious, prevPointer, kc.regs .r8 (by decide),
      kc.regs .rbx (by decide), kc.regs .rdi (by decide), kc.regs .r12 (by decide),
      kb.regs .r8 (by decide), ka.regs .r8 (by decide), kb.regs .rbx (by decide),
      ka.regs .rbx (by decide), kb.regs .r12 (by decide), ka.regs .r12 (by decide), prevColumn]
    change address _ _ ((if column a = 0 then a.gpr .r12 else column a) - 1) _ = _
    rw [coords, ka.regs .r12 (by decide), predecessor]
  · rw [referenceResult, refPointer, kd.regs .r8 (by decide), kd.regs .r9 (by decide),
      kd.regs .rsi (by decide), kd.regs .r12 (by decide), kc.regs .r8 (by decide),
      kc.regs .r9 (by decide), kc.regs .rsi (by decide), kc.regs .r12 (by decide),
      kb.regs .r8 (by decide), kb.regs .r9 (by decide), kb.regs .rsi (by decide),
      kb.regs .r12 (by decide), ka.regs .r8 (by decide), ka.regs .r9 (by decide),
      ka.regs .r12 (by decide), refColumn]
  · exact (((((ka.mono (by simp [changed])).trans (kb.mono (by simp [changed]))).trans
      (kc.mono (by simp [changed]))).trans (kd.mono (by simp [changed]))).trans
      (ke.mono (by simp [changed]))).trans (kt.mono (by simp [changed]))

end VG.Proof.Argon2.X86_64.FillPointers
end

/-! Matrix pointers are the natural-number block offsets in the specification. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

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
    (rl : s.gpr .r9 = BitVec.ofNat 64 refLane)
    (rc : s.gpr .rdi = BitVec.ofNat 64 refColumn) :
    WP isa code s fun t =>
      t.gpr .r10 = cell (s.gpr .r8) p lane (slice * p.segmentLen + index) ∧
      t.gpr .rdi = cell (s.gpr .r8) p lane ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) ∧
      t.gpr .rsi = cell (s.gpr .r8) p refLane refColumn ∧ Divide.Keeps changed s t := by
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

end VG.Proof.Argon2.X86_64.FillPointers
end

/-! Merged from `Proof.Argon2.X86_64.FillKernelLayout`. -/
section
/-! One allocation invariant covers all matrix cells used by the filling step. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 232) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

structure Layout (p : Params) (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 184, 232, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .rbp) 16) 8
  matrixWrite : Covers [⟨matrix s, p.blocks * 1024⟩] s.wr
  workWrite : Covers [⟨work s, 5120⟩] s.wr
  matrixWork : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨work s, 5120⟩
  matrixFrame : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  matrixStack : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨work s, 5120⟩
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨work s, 5120⟩

theorem Layout.of_keeps {p : Params} {s t : State} (h : Layout p s)
    (k : Divide.Keeps ReferenceMap.changed s t) : Layout p t := by
  have bp := k.regs .rbp (by decide)
  have sp := k.regs .rsp (by decide)
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
    (left : s.gpr .rdi = FillPointers.cell (matrix s) p leftLane leftColumn)
    (right : s.gpr .rsi = FillPointers.cell (matrix s) p rightLane rightColumn)
    (dest : s.gpr .r10 = FillPointers.cell (matrix s) p destLane destColumn) : FillCompress.Ready s := by
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

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Reload frame arguments and compose reference mapping with matrix addresses. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem load_ok (s : State) (r : Reg) (d : Nat)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    WP isa (.block [.mov r (.mem (Impl.Argon2.X86_64.at_ .rbp d))]) s fun t =>
      t.gpr r = s.mem.readW (off (s.gpr .rbp) d) 64 ∧ Divide.Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, read, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ite_eq_right hq
  all_goals rfl

structure Ready (p : Params) (pass lane slice index : Nat) (s : State) : Prop where
  layout : Layout p s
  bounds : ReferenceMap.Bounds p pass lane slice index
  position : ReferenceMap.Position p lane slice index s
  passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

structure Mapped (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).1
  column : t.gpr .rdi = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).2
  original : t.gpr .r11 = s.gpr .rdi
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem mapping_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.X86_64.FillKernel.mapping s (Mapped s · p pass lane slice index) := by
  unfold Impl.Argon2.X86_64.FillKernel.mapping
  refine WP.seq ((load_ok s .rsi 184 (h.layout.frameRead 184 (by simp))).mono ?_)
  rintro a ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have ready : ReferenceMap.Ready p pass lane slice index a := by
    refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩
    · rw [k.rd, k.wr, k.regs .rbp (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
        using h.layout.frameRead 0 (by simp)
    · rw [k.mem, k.regs .rbp (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord
  refine (ReferenceMap.code_spec_ok a p pass lane slice index ready).mono ?_
  rintro t ⟨lane, column, original, tail⟩
  rw [keeps.regs .rdi (by decide)] at lane column original
  exact ⟨lane, column, original, k.trans tail⟩

structure Pointers (s t : State) (p : Params) (lane slice index refLane refColumn : Nat) : Prop where
  current : t.gpr .r10 = FillPointers.cell (matrix s) p lane (slice * p.segmentLen + index)
  previous : t.gpr .rdi = FillPointers.cell (matrix s) p lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen)
  reference : t.gpr .rsi = FillPointers.cell (matrix s) p refLane refColumn
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem pointers_ok (s : State) (p : Params) (pass lane slice index refLane refColumn : Nat)
    (layout : Layout p s) (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (laneWord : s.gpr .r9 = BitVec.ofNat 64 refLane) (columnWord : s.gpr .rdi = BitVec.ofNat 64 refColumn) :
    WP isa Impl.Argon2.X86_64.FillKernel.pointers s (Pointers s · p lane slice index refLane refColumn) := by
  unfold Impl.Argon2.X86_64.FillKernel.pointers
  refine WP.seq ((load_ok s .r8 232 (layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have lane' : a.gpr .r9 = BitVec.ofNat 64 refLane := (keeps.regs .r9 (by decide)).trans laneWord
  have col' : a.gpr .rdi = BitVec.ofNat 64 refColumn := (keeps.regs .rdi (by decide)).trans columnWord
  refine (FillPointers.code_nat_ok a p pass lane slice index refLane refColumn bounds
    (position.of_keeps k) lane' col').mono ?_
  rintro t ⟨current, previous, reference, tail⟩
  rw [base] at current previous reference
  exact ⟨current, previous, reference, k.trans (tail.mono (by decide))⟩

end VG.Proof.Argon2.X86_64.FillKernel

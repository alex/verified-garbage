import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.X86_64.CountCandidates

/-! The reference window starts at the next slice on later passes. -/

namespace VG.Proof.Argon2.X86_64.ReferenceStart

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceStart

theorem sub_zero_iff (x y : Addr) : x - y = 0 ↔ x = y := by
  constructor
  · intro h
    calc
      x = (x - y) + y := (BitVec.sub_add_cancel x y).symm
      _ = y := by rw [h]; exact BitVec.zero_add y
  · intro h; rw [h, BitVec.sub_self]; rfl

theorem zero_ok (s : State) : WP isa (.block zero) s fun t =>
    t.gpr .r10 = 0 ∧ Divide.Keeps [.r10] s t := by
  apply WP.of_runBlock
  simp only [zero, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    RegUpd.gpr_setReg, Option.map_some, Option.some.injEq, exists_eq_left',
    ite_true, show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem advance_ok (s : State) : WP isa (.block advance) s fun t =>
    t.gpr .r10 = (s.gpr .r14 + 1) * s.gpr .r13 ∧
    t.zf = decide (s.gpr .r14 = 3) ∧ Divide.Keeps [.rax, .rdx, .r10] s t := by
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, execMul, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    RegUpd.zf_arithFlags, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (3 : BitVec 32) = (3 : Addr) from rfl]
  refine ⟨trivial, ?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, sub_zero_iff]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
        hr.1, hr.2.1, hr.2.2, ite_false]
    all_goals rfl

def changed : List Reg := [.rax, .rdx, .r10]

def value (s : State) : Addr :=
  if s.gpr .r9 = 0 then 0 else
    if s.gpr .r14 = 3 then 0 else (s.gpr .r14 + 1) * s.gpr .r13

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .r10 = value s ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .r9 = 0)) (by simp only [eval, flag]) ?_ ?_
  · intro h
    have firstPass : s.gpr .r9 = 0 := of_decide_eq_true h
    refine (zero_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by simp)).trans (tail.mono (by decide))⟩
    simpa only [value, firstPass, ite_true] using out
  · intro h
    have laterPass : s.gpr .r9 ≠ 0 := of_decide_eq_false h
    refine WP.seq ((advance_ok a).mono ?_)
    rintro b ⟨out, flag, advanceKeeps⟩
    have sliceReg := keeps.regs .r14 (by simp)
    have segmentReg := keeps.regs .r13 (by simp)
    refine WP.ite (decide (s.gpr .r14 = 3))
      (by simp only [eval, flag, sliceReg]) ?_ ?_
    · intro h
      have lastSlice : s.gpr .r14 = 3 := of_decide_eq_true h
      refine (zero_ok b).mono ?_
      rintro t ⟨out, tail⟩
      refine ⟨?_, ((keeps.mono (by simp)).trans advanceKeeps).trans (tail.mono (by decide))⟩
      simpa only [value, laterPass, lastSlice, ite_false, ite_true] using out
    · intro h
      have earlierSlice : s.gpr .r14 ≠ 3 := of_decide_eq_false h
      apply WP.of_runBlock
      simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
      refine ⟨?_, (keeps.mono (by simp)).trans advanceKeeps⟩
      simpa only [value, laterPass, earlierSlice, ite_false, sliceReg, segmentReg] using out

theorem start_nat (p : Spec.Argon2.Params) (hl : 0 < p.lanes)
    (hg : 0 < p.segmentLen) (slice : Nat) (hs : slice < 4) :
    (slice + 1) * p.segmentLen % p.laneLen =
      if slice = 3 then 0 else (slice + 1) * p.segmentLen := by
  rw [Proof.Argon2.laneLen_segments p hl]
  by_cases lastSlice : slice = 3
  · simp only [lastSlice, ite_true, show (3 : Nat) + 1 = 4 from rfl, Nat.mod_self]
  · have smaller : (slice + 1) * p.segmentLen < 4 * p.segmentLen :=
      Nat.mul_lt_mul_of_pos_right (by omega) hg
    rw [Nat.mod_eq_of_lt smaller]
    simp only [lastSlice, ite_false]

theorem value_nat (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (hl : 0 < p.lanes) (hg : 0 < p.segmentLen) (hs : slice < 4)
    (passReg : (s.gpr .r9).toNat = pass)
    (sliceReg : s.gpr .r14 = BitVec.ofNat 64 slice)
    (segmentReg : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen) :
    value s = BitVec.ofNat 64
      (if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen) := by
  have isZero : s.gpr .r9 = 0 ↔ pass = 0 := by
    rw [← passReg]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      apply BitVec.eq_of_toNat_eq
      exact h
  have isLast : s.gpr .r14 = 3 ↔ slice = 3 := by
    rw [sliceReg]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
      exact hn
    · intro h; rw [h]; rfl
  unfold value
  simp only [isZero, isLast]
  by_cases firstPass : pass = 0
  · simp only [firstPass, ite_true]; rfl
  · simp only [firstPass, ite_false, start_nat p hl hg slice hs]
    by_cases lastSlice : slice = 3
    · simp only [lastSlice, ite_true]; rfl
    · simp only [lastSlice, ite_false]
      rw [sliceReg, segmentReg]
      change (BitVec.ofNat 64 slice + BitVec.ofNat 64 1) *
        BitVec.ofNat 64 p.segmentLen = _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_mul]

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (hl : 0 < p.lanes) (hg : 0 < p.segmentLen) (hs : slice < 4)
    (passReg : (s.gpr .r9).toNat = pass)
    (sliceReg : s.gpr .r14 = BitVec.ofNat 64 slice)
    (segmentReg : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen) :
    WP isa code s fun t =>
      t.gpr .r10 = BitVec.ofNat 64
        (if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen) ∧
      Divide.Keeps changed s t :=
  (code_ok s).mono (fun _ h =>
    ⟨h.1.trans (value_nat s p pass slice hl hg hs passReg sliceReg segmentReg), h.2⟩)

end VG.Proof.Argon2.X86_64.ReferenceStart

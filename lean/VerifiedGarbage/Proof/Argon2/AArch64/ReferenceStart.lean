import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.AArch64.CountCandidates

/-! The reference window starts at the next slice on later passes. -/

namespace VG.Proof.Argon2.AArch64.ReferenceStart

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceStart
open VG.Impl.Argon2.AArch64

theorem sub_zero_iff (x y : Addr) : x - y = 0 ↔ x = y := by
  constructor
  · intro h
    calc
      x = (x - y) + y := (BitVec.sub_add_cancel x y).symm
      _ = y := by rw [h]; exact BitVec.zero_add y
  · intro h; rw [h, BitVec.sub_self]; rfl

theorem zero_ok (s : State) : WP isa (.block zero) s fun t =>
    t.gpr .x6 = 0 ∧ Divide.Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [zero, Instructions.imm, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, Size.bits, Nat.reduceMul, Nat.reduceLT, ite_true,
    BitVec.shiftLeft_zero, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem advance_ok (s : State) : WP isa (.block advance) s fun t =>
    t.gpr .x6 = (s.gpr .x22 + 1) * s.gpr .x21 ∧
    t.gpr .x15 = s.gpr .x22 - 3 ∧ Divide.Keeps [.x8, .x2, .x6, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [advance, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.addi, Instructions.mul, Instructions.mark,
    Instructions.comparei, Instructions.compare, Instructions.imm,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', Bool.toNat_true,
    show 1 < 4096 from by decide, show 0 < 4096 from by decide,
    show 3 < 65536 from by decide,
    show (BitVec.ofNat 16 3).setWidth 64 = 3#64 from rfl,
    show (3#64) = (3 : Addr) from rfl,
    show (BitVec.ofNat 64 1) = (1 : Addr) from rfl]
  refine ⟨trivial, sub_value _ _, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
  all_goals rfl

def changed : List Reg := [.x8, .x2, .x6, .x13, .x14, .x15]

def value (s : State) : Addr :=
  if s.gpr .x5 = 0 then 0 else
    if s.gpr .x22 = 3 then 0 else (s.gpr .x22 + 1) * s.gpr .x21

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x6 = value s ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .x5 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
  · intro h
    have firstPass : s.gpr .x5 = 0 := of_decide_eq_true h
    refine (zero_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [value, firstPass, ite_true] using out
  · intro h
    have laterPass : s.gpr .x5 ≠ 0 := of_decide_eq_false h
    refine WP.seq ((advance_ok a).mono ?_)
    rintro b ⟨out, flag, advanceKeeps⟩
    have sliceReg := keeps.regs .x22 (by simp)
    have segmentReg := keeps.regs .x21 (by simp)
    refine WP.ite (decide (s.gpr .x22 = 3))
      (by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, sliceReg]
        apply congrArg some
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, decide_eq_true_eq]
        exact sub_zero_iff _ _) ?_ ?_
    · intro h
      have lastSlice : s.gpr .x22 = 3 := of_decide_eq_true h
      refine (zero_ok b).mono ?_
      rintro t ⟨out, tail⟩
      refine ⟨?_, ((keeps.mono (by decide)).trans advanceKeeps).trans (tail.mono (by decide))⟩
      simpa only [value, laterPass, lastSlice, ite_false, ite_true] using out
    · intro h
      have earlierSlice : s.gpr .x22 ≠ 3 := of_decide_eq_false h
      apply WP.of_runBlock
      simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
      refine ⟨?_, (keeps.mono (by decide)).trans advanceKeeps⟩
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
    (passReg : (s.gpr .x5).toNat = pass)
    (sliceReg : s.gpr .x22 = BitVec.ofNat 64 slice)
    (segmentReg : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen) :
    value s = BitVec.ofNat 64
      (if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen) := by
  have isZero : s.gpr .x5 = 0 ↔ pass = 0 := by
    rw [← passReg]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      apply BitVec.eq_of_toNat_eq
      exact h
  have isLast : s.gpr .x22 = 3 ↔ slice = 3 := by
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
    (passReg : (s.gpr .x5).toNat = pass)
    (sliceReg : s.gpr .x22 = BitVec.ofNat 64 slice)
    (segmentReg : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen) :
    WP isa code s fun t =>
      t.gpr .x6 = BitVec.ofNat 64
        (if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen) ∧
      Divide.Keeps changed s t :=
  (code_ok s).mono (fun _ h =>
    ⟨h.1.trans (value_nat s p pass slice hl hg hs passReg sliceReg segmentReg), h.2⟩)

end VG.Proof.Argon2.AArch64.ReferenceStart

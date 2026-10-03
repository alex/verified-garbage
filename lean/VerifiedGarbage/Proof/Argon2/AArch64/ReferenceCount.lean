import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceCount
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.AArch64.CountCandidates
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Argon2.AArch64.CountCandidates
import VerifiedGarbage.Impl.Argon2.AArch64.SelectWindow
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep

/-! Merged from `Proof.Argon2.AArch64.SelectWindow`. -/
section
/-! # Same-lane window selection with no leakage from the equality test -/

namespace VG.Proof.Argon2.AArch64.SelectWindow

open VG VG.AArch64 VG.Impl.Argon2.AArch64.SelectWindow
open VG.Impl.Argon2.AArch64

theorem equality_test (x y : Addr) : (x ^^^ y).toNat < 1 ↔ x = y := by
  constructor
  · intro h
    have zero : x ^^^ y = 0 := by
      apply BitVec.eq_of_toNat_eq
      change (x ^^^ y).toNat = 0
      omega
    exact BitVec.xor_eq_zero_iff.mp zero
  · intro h
    rw [h, BitVec.xor_self]
    decide

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x4 = (if s.gpr .x0 = s.gpr .x1 then s.gpr .x2 else s.gpr .x3) ∧
    Divide.Keeps [.x8, .x4, .x2, .x12, .x15] s t := by
  unfold code
  apply WP.of_runBlock
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.subi, Instructions.sub, Instructions.sbb,
    Instructions.logic, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    show (1#64).toNat = 1 from rfl, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', Bool.toNat_true, sub_value, sub_carry,
    borrow_mask]
  have hm : (if decide (1 ≤ (s.gpr .x0 ^^^ s.gpr .x1).toNat) then 0 else -1) =
      Divide.mask (decide ((s.gpr .x0 ^^^ s.gpr .x1).toNat < 1)) := by
    by_cases h : (s.gpr .x0 ^^^ s.gpr .x1).toNat < 1
    · simp only [Divide.mask, h, Nat.not_le_of_gt h, decide_false, decide_true,
        Bool.false_eq_true, ite_false, ite_true]
    · simp only [Divide.mask, h, Nat.le_of_not_gt h, decide_false, decide_true,
        Bool.false_eq_true, ite_false, ite_true]
  rw [hm, Divide.select_value]
  simp only [decide_eq_true_eq, equality_test]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.SelectWindow
end

/-! Merged from `Proof.Argon2.AArch64.CountCandidatesLit`. -/
section
/-! Checked instruction literal for reference-window arithmetic. -/
namespace VG
materialize_code Impl.Argon2.AArch64.CountCandidates.code
end VG
end

/-! Merged from `Proof.Argon2.AArch64.CountCandidatesCT`. -/
section
/-! Only the public pass controls reference-window arithmetic. -/
namespace VG.Proof.Argon2.AArch64.CountCandidates
open VG VG.AArch64 VG.Impl.Argon2.AArch64.CountCandidates

theorem code_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x5 = t.gpr .x5) code
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x5])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h.2⟩) [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64.CountCandidates
end

/-! The selected reference window, with public pass control only. -/

namespace VG.Proof.Argon2.AArch64.ReferenceCount

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceCount

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x4 = (if s.gpr .x0 = s.gpr .x1 then
      CountCandidates.base s + s.gpr .x23 - 1 else
      CountCandidates.base s + Divide.mask (decide ((s.gpr .x23).toNat < 1))) ∧
    Divide.Keeps CountCandidates.changed s t := by
  unfold code
  refine WP.seq ((CountCandidates.code_ok s).mono ?_)
  rintro a ⟨same, other, keeps⟩
  refine (SelectWindow.code_ok a).mono ?_
  rintro t ⟨out, tail⟩
  refine ⟨?_, keeps.trans (tail.mono (by decide))⟩
  rw [out, keeps.regs .x0 (by decide), keeps.regs .x1 (by decide), same, other]

theorem same_word (b i : Nat) (positive : 0 < b + i) :
    BitVec.ofNat 64 b + BitVec.ofNat 64 i - (1 : Addr) =
      BitVec.ofNat 64 (b + i - 1) := by
  rw [← BitVec.ofNat_add]
  change BitVec.ofNat 64 (b + i) - BitVec.ofNat 64 1 = _
  exact Offset.ofNat_sub_ofNat (by omega)

theorem other_word (b i : Nat) (bound : i < 2 ^ 64) (positive : i = 0 → 0 < b) :
    BitVec.ofNat 64 b + Divide.mask (decide ((BitVec.ofNat 64 i).toNat < 1)) =
      BitVec.ofNat 64 (b - (if i = 0 then 1 else 0)) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  by_cases zero : i = 0
  · simp only [zero, show decide ((0 : Nat) < 1) = true from rfl, Divide.mask, ite_true]
    rw [BitVec.add_neg_eq_sub]
    change BitVec.ofNat 64 b - BitVec.ofNat 64 1 = _
    exact Offset.ofNat_sub_ofNat (by have := positive zero; omega)
  · have notSmall : ¬i < 1 := by omega
    simp only [notSmall, decide_false, Divide.mask, Bool.false_eq_true, ite_false,
      zero, Nat.sub_zero]
    change BitVec.ofNat 64 b + 0#64 = BitVec.ofNat 64 b
    rw [BitVec.add_zero]

theorem selected_word (b i : Nat) (same : Bool) (bound : i < 2 ^ 64)
    (positive : 0 < b + i) (atZero : i = 0 → 0 < b) :
    (if same then BitVec.ofNat 64 b + BitVec.ofNat 64 i - (1 : Addr) else
      BitVec.ofNat 64 b + Divide.mask (decide ((BitVec.ofNat 64 i).toNat < 1))) =
      BitVec.ofNat 64 (if same then b + i - 1 else b - (if i = 0 then 1 else 0)) := by
  cases same
  · exact other_word b i bound atZero
  · exact same_word b i positive

theorem spec_count (p : Spec.Argon2.Params) (pass slice index : Nat) (same : Bool) :
    Spec.Argon2.referenceCount p pass slice index same =
      let b := if pass = 0 then slice * p.segmentLen else p.laneLen - p.segmentLen
      if same then b + index - 1 else b - (if index = 0 then 1 else 0) := by
  unfold Spec.Argon2.referenceCount
  by_cases firstPass : pass = 0 <;> cases same <;>
    simp only [firstPass, ite_true, ite_false, Bool.false_eq_true]

def windowBase (p : Spec.Argon2.Params) (pass slice : Nat) : Nat :=
  if pass = 0 then slice * p.segmentLen else p.laneLen - p.segmentLen

theorem base_nat (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (passReg : (s.gpr .x5).toNat = pass)
    (laneReg : s.gpr .x20 = BitVec.ofNat 64 p.laneLen)
    (segmentReg : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen)
    (sliceReg : s.gpr .x22 = BitVec.ofNat 64 slice)
    (segmentBound : p.segmentLen ≤ p.laneLen) :
    CountCandidates.base s = BitVec.ofNat 64 (windowBase p pass slice) := by
  have isZero : s.gpr .x5 = 0 ↔ pass = 0 := by
    rw [← passReg]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      apply BitVec.eq_of_toNat_eq
      exact h
  unfold CountCandidates.base windowBase
  by_cases firstPass : pass = 0
  · simp only [isZero, firstPass, ite_true]
    rw [segmentReg, sliceReg, ← BitVec.ofNat_mul, Nat.mul_comm]
  · simp only [isZero, firstPass, ite_false]
    rw [laneReg, segmentReg]
    exact Offset.ofNat_sub_ofNat segmentBound

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass slice index : Nat)
    (passReg : (s.gpr .x5).toNat = pass)
    (laneReg : s.gpr .x20 = BitVec.ofNat 64 p.laneLen)
    (segmentReg : s.gpr .x21 = BitVec.ofNat 64 p.segmentLen)
    (sliceReg : s.gpr .x22 = BitVec.ofNat 64 slice)
    (indexReg : s.gpr .x23 = BitVec.ofNat 64 index)
    (segmentBound : p.segmentLen ≤ p.laneLen) (indexBound : index < 2 ^ 64)
    (positive : 0 < windowBase p pass slice + index)
    (atZero : index = 0 → 0 < windowBase p pass slice) :
    WP isa code s fun t =>
      t.gpr .x4 = BitVec.ofNat 64 (Spec.Argon2.referenceCount p pass slice index
        (decide (s.gpr .x0 = s.gpr .x1))) ∧
      Divide.Keeps CountCandidates.changed s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨out, keeps⟩
  refine ⟨out.trans ?_, keeps⟩
  rw [base_nat s p pass slice passReg laneReg segmentReg sliceReg segmentBound, indexReg,
    spec_count]
  simpa only [decide_eq_true_eq, windowBase] using
    selected_word (windowBase p pass slice) index
      (decide (s.gpr .x0 = s.gpr .x1)) indexBound positive atZero

theorem code_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x5 = t.gpr .x5) code
    (fun s t => s.sp = t.sp) :=
  CountCandidates.code_rel.seq SelectWindow.code_secret_rel

end VG.Proof.Argon2.AArch64.ReferenceCount

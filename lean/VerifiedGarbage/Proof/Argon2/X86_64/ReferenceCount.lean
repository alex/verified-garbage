import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceCount
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.X86_64.CountCandidates
import VerifiedGarbage.Proof.Argon2.X86_64.CountCandidatesCT
import VerifiedGarbage.Proof.Argon2.X86_64.SelectWindow

/-! The selected reference window, with public pass control only. -/

namespace VG.Proof.Argon2.X86_64.ReferenceCount

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceCount

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .r8 = (if s.gpr .rdi = s.gpr .rsi then
      CountCandidates.base s + s.gpr .r15 - 1 else
      CountCandidates.base s + Divide.mask (decide ((s.gpr .r15).toNat < 1))) ∧
    Divide.Keeps CountCandidates.changed s t := by
  unfold code
  refine WP.seq ((CountCandidates.code_ok s).mono ?_)
  rintro a ⟨same, other, keeps⟩
  refine (SelectWindow.code_ok a).mono ?_
  rintro t ⟨out, tail⟩
  refine ⟨?_, keeps.trans (tail.mono (by decide))⟩
  rw [out, keeps.regs .rdi (by decide), keeps.regs .rsi (by decide), same, other]

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
    (passReg : (s.gpr .r9).toNat = pass)
    (laneReg : s.gpr .r12 = BitVec.ofNat 64 p.laneLen)
    (segmentReg : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen)
    (sliceReg : s.gpr .r14 = BitVec.ofNat 64 slice)
    (segmentBound : p.segmentLen ≤ p.laneLen) :
    CountCandidates.base s = BitVec.ofNat 64 (windowBase p pass slice) := by
  have isZero : s.gpr .r9 = 0 ↔ pass = 0 := by
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
    (passReg : (s.gpr .r9).toNat = pass)
    (laneReg : s.gpr .r12 = BitVec.ofNat 64 p.laneLen)
    (segmentReg : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen)
    (sliceReg : s.gpr .r14 = BitVec.ofNat 64 slice)
    (indexReg : s.gpr .r15 = BitVec.ofNat 64 index)
    (segmentBound : p.segmentLen ≤ p.laneLen) (indexBound : index < 2 ^ 64)
    (positive : 0 < windowBase p pass slice + index)
    (atZero : index = 0 → 0 < windowBase p pass slice) :
    WP isa code s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (Spec.Argon2.referenceCount p pass slice index
        (decide (s.gpr .rdi = s.gpr .rsi))) ∧
      Divide.Keeps CountCandidates.changed s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨out, keeps⟩
  refine ⟨out.trans ?_, keeps⟩
  rw [base_nat s p pass slice passReg laneReg segmentReg sliceReg segmentBound, indexReg,
    spec_count]
  simpa only [decide_eq_true_eq, windowBase] using
    selected_word (windowBase p pass slice) index
      (decide (s.gpr .rdi = s.gpr .rsi)) indexBound positive atZero

theorem code_rel : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9) code
    (fun _ _ => True) :=
  CountCandidates.code_rel.seq SelectWindow.code_secret_rel

end VG.Proof.Argon2.X86_64.ReferenceCount

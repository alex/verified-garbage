import VerifiedGarbage.Impl.Argon2.AArch64.SelectWindow
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

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

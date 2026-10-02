import VerifiedGarbage.Impl.Argon2.AArch64.Wrap
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! # Masked subtraction agrees with wrapping the reference column -/

namespace VG.Proof.Argon2.AArch64.Wrap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Wrap
open VG.Impl.Argon2.AArch64

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x0 = (if (s.gpr .x0).toNat < (s.gpr .x1).toNat
      then s.gpr .x0 else s.gpr .x0 - s.gpr .x1) ∧
    Divide.Keeps [.x0, .x6, .x8, .x15] s t := by
  unfold code
  apply WP.of_runBlock
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.sub, Instructions.sbb, Instructions.logic,
    Instructions.mark, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', Bool.toNat_true, sub_value, sub_carry,
    borrow_mask]
  have hm : (if decide ((s.gpr .x1).toNat ≤ (s.gpr .x0).toNat) then 0 else -1) =
      Divide.mask (decide ((s.gpr .x0).toNat < (s.gpr .x1).toNat)) := by
    by_cases h : (s.gpr .x0).toNat < (s.gpr .x1).toNat <;>
      simp [Divide.mask, h, Nat.le_of_not_gt, Nat.not_le_of_gt]
  rw [hm, Divide.select_value]
  simp only [decide_eq_true_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem wrap_nat (x q : Addr) (bound : x.toNat < 2 * q.toNat) :
    (if x.toNat < q.toNat then x else x - q) = BitVec.ofNat 64 (x.toNat % q.toNat) := by
  rw [Proof.Argon2.reference_wrap _ _ bound]
  by_cases small : x.toNat < q.toNat
  · rw [ite_eq_left small, ite_eq_left small]
    exact (BitVec.ofNat_toNat 64 x).symm
  · rw [ite_eq_right small, ite_eq_right small]
    calc
      x - q = BitVec.ofNat 64 x.toNat - BitVec.ofNat 64 q.toNat := by
        simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := Offset.ofNat_sub_ofNat (by omega)

theorem code_nat_ok (s : State) (bound : (s.gpr .x0).toNat < 2 * (s.gpr .x1).toNat) :
    WP isa code s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 ((s.gpr .x0).toNat % (s.gpr .x1).toNat) ∧
      Divide.Keeps [.x0, .x6, .x8, .x15] s t :=
  (code_ok s).mono (fun _ h => ⟨h.1.trans (wrap_nat _ _ bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.Wrap

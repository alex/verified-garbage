import VerifiedGarbage.Impl.Argon2.X86_64.Wrap
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # Masked subtraction agrees with wrapping the reference column -/

namespace VG.Proof.Argon2.X86_64.Wrap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Wrap

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .rdi = (if (s.gpr .rdi).toNat < (s.gpr .rsi).toNat
      then s.gpr .rdi else s.gpr .rdi - s.gpr .rsi) ∧
    Divide.Keeps [.rdi, .r10, .rax] s t := by
  unfold code
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg,     RegUpd.gpr_arithFlags,     RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, Divide.select_value, decide_eq_true_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2,
      ite_false]
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

theorem code_nat_ok (s : State) (bound : (s.gpr .rdi).toNat < 2 * (s.gpr .rsi).toNat) :
    WP isa code s fun t =>
      t.gpr .rdi = BitVec.ofNat 64 ((s.gpr .rdi).toNat % (s.gpr .rsi).toNat) ∧
      Divide.Keeps [.rdi, .r10, .rax] s t :=
  (code_ok s).mono (fun _ h => ⟨h.1.trans (wrap_nat _ _ bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun _ _ => True) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.Wrap

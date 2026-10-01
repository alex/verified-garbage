import VerifiedGarbage.Impl.Argon2.X86_64.SelectWindow
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # Same-lane window selection with no leakage from the equality test -/

namespace VG.Proof.Argon2.X86_64.SelectWindow

open VG VG.X86_64 VG.Impl.Argon2.X86_64.SelectWindow

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
    t.gpr .r8 = (if s.gpr .rdi = s.gpr .rsi then s.gpr .rdx else s.gpr .rcx) ∧
    Divide.Keeps [.rax, .r8, .rdx] s t := by
  unfold code
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show (1 : Addr).toNat = 1 from rfl, equality_test, Divide.sbb_mask, Divide.select_value, decide_eq_true_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem code_secret_rel : RelCT isa (fun _ _ => True) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.SelectWindow

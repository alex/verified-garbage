import VerifiedGarbage.Proof.X448.Wide.CarryStep

/-! Untrusted: initialize the carry, zero register, and 56-bit mask. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem passInit_ok (s : State) :
    WP isa (.block passInit) s fun t =>
      t.gpr .x6 = 0 ∧ t.gpr .x11 = 0 ∧ t.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) ∧
      t.mem = s.mem ∧ Keeps colRegs s t := by
  apply WP.of_runBlock
  simp only [passInit, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceMul, Nat.reduceLT, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · decide
  · simp only [colRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.X448.Wide

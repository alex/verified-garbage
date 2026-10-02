import VerifiedGarbage.Proof.X448.Wide.CarryRegs
import VerifiedGarbage.Proof.X448.AArch64.Step

/-! Untrusted: split a wide digit into two normalized interface limbs. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem unpackRegs_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12]) s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x4).toNat % VG.Proof.X448.radix ∧
      (t.gpr .x5).toNat = (s.gpr .x4).toNat / VG.Proof.X448.radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, hs.mask, Option.some.injEq, exists_eq_left']
  refine ⟨and28 _, shr28 _, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.X448.Wide

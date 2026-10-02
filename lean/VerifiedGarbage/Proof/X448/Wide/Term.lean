import VerifiedGarbage.Impl.X448.AArch64.Wide
import VerifiedGarbage.Proof.X448.Wide.Word
import VerifiedGarbage.Proof.X448.AArch64.Mem

/-! Untrusted: the register-only multiply-add used by wide X448 columns. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Impl.X448.AArch64.Wide VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi read_x)
open VG.Proof.X448.AArch64 (Keeps)

theorem term_ok (s : State)
    (h : (s.gpr .x6).toNat * (s.gpr .x9).toNat + pair (s.gpr .x4) (s.gpr .x5) < 2 ^ 128) :
    WP isa (.block term) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) =
        (s.gpr .x6).toNat * (s.gpr .x9).toNat + pair (s.gpr .x4) (s.gpr .x5) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [term, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · have hm := madd128 (s.gpr .x6) (s.gpr .x9) (s.gpr .x4) (s.gpr .x5) h
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at hm ⊢
    exact hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

end VG.Proof.X448.Wide

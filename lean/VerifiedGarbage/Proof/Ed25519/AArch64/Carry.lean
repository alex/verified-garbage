import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Ed25519.Field64

/-! Reduction of the carry above four 64-bit field limbs. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

private theorem carry38_word (c : Bool) :
    addCarry 0 0 c * 38 = BitVec.ofNat 64 (38 * c.toNat) := by
  cases c <;> decide

private theorem carry38_arith (a0 a1 a2 a3 v : Word) (hv : v.toNat < 2 ^ 58) :
    let c0 := carryOut a0 v false
    let c1 := carryOut a1 0 c0
    let c2 := carryOut a2 0 c1
    let c3 := carryOut a3 0 c2
    toFe (val4 (addCarry a0 v false + addCarry 0 0 c3 * 38)
      (addCarry a1 0 c0) (addCarry a2 0 c1) (addCarry a3 0 c2)) =
      toFe (val4 a0 a1 a2 a3 + v.toNat) := by
  intro c0 c1 c2 c3
  rw [carry38_word]
  apply foldCarry_field _ _ _ _ _ (val4_lt a0 a1 a2 a3) hv
  simpa only [val4, Bool.toNat_false, Nat.add_zero, Nat.mul_zero, show (0 : Word).toNat = 0 from rfl] using
    add4_value a0 a1 a2 a3 v 0 0 0 false

theorem carry38_ok (s : State) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38)
    (hv : (s.gpr .x8).toNat < 2 ^ 58) :
    WP isa (.block carry38) s fun s' =>
      toFe (val4 (s'.gpr .x4) (s'.gpr .x5) (s'.gpr .x6) (s'.gpr .x7)) =
        toFe (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + (s.gpr .x8).toNat) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s s' := by
  apply WP.of_runBlock
  simp only [carry38, carryValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz, h38,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := carry38_arith (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) hv
    dsimp only [addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64

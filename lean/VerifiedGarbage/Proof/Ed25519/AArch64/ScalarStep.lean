import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Ed25519.Canonical64

/-! Untrusted: the conditional subtraction of the Ed25519 order from a four-word value. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64
open VG.Spec.Ed25519 (L)

def scalarValue (s : State) : Nat := val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
def savedValue (s : State) : Nat := val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)

theorem order_limbs : val4 orderLo orderHi 0 orderTop = L := by decide

theorem subtract_chain (a b c d : Word) :
    let c0 := carryOut a (~~~orderLo) true
    let c1 := carryOut b (~~~orderHi) c0
    let c2 := carryOut c (~~~0) c1
    let c3 := carryOut d (~~~orderTop) c2
    let v := val4 (addCarry a (~~~orderLo) true) (addCarry b (~~~orderHi) c0)
      (addCarry c (~~~0) c1) (addCarry d (~~~orderTop) c2)
    c3 = decide (L ≤ val4 a b c d) ∧
      v + L = val4 a b c d + 2 ^ 256 * (1 - c3.toNat) := by
  intro c0 c1 c2 c3 v
  have e : v + val4 orderLo orderHi 0 orderTop = val4 a b c d + 2 ^ 256 * (1 - c3.toNat) := by
    simpa only [Bool.toNat_true, Nat.sub_self, Nat.add_zero] using
      sub4_value a b c d orderLo orderHi 0 orderTop true
  rw [order_limbs] at e
  have hv : v < 2 ^ 256 := val4_lt _ _ _ _
  have hx := val4_lt a b c d
  clear_value v c3 c2 c1 c0
  refine ⟨?_, e⟩
  cases c3 <;> simp only [Bool.toNat_false, Bool.toNat_true] at e
  · exact (decide_eq_false (by omega)).symm
  · exact (decide_eq_true (by omega)).symm

theorem scalarSubtract_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block scalarSubtract) s fun t =>
      t.c = decide (L ≤ scalarValue s) ∧
      scalarValue t + L = scalarValue s + 2 ^ 256 * (1 - (decide (L ≤ scalarValue s)).toNat) ∧
      savedValue t = scalarValue s ∧
      Keeps [.x3, .x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [scalarSubtract, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, mov, exec, read_x,
    show (0 : Nat) < 4096 from by decide,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    scalarValue, savedValue, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    RegUpd.c_write, RegUpd.c_addWithCarry, BitVec.setWidth_eq, BitVec.add_zero,
    hz, ite_true, ite_false, reduceCtorEq, movz_movk64', Option.some.injEq, exists_eq_left']
  have H := subtract_chain (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
  refine ⟨?_, ?_, True.intro, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits, scalarValue] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits, scalarValue] at H ⊢
    exact H.2.trans (congrArg (fun c : Bool =>
      val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + 2 ^ 256 * (1 - c.toNat)) H.1)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem carry_mask (c : Bool) : addCarry 0 (~~~0) c = mask (!c) := by
  cases c <;> decide

theorem scalarSelect_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block scalarSelect) s fun t =>
      scalarValue t = (if !s.c then savedValue s else scalarValue s) ∧
      Keeps [.x8, .x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [scalarSelect, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    scalarValue, savedValue, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, hz, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have hm := carry_mask s.c
  dsimp only [addCarry] at hm
  simp only [hm, xor_sel']
  refine ⟨by cases s.c <;> rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
    hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem select_remainder (x y : Nat) (hx : x < 2 * L)
    (he : y + L = x + 2 ^ 256 * (1 - (decide (L ≤ x)).toNat)) :
    (if L ≤ x then y else x) = x % L := by
  by_cases h : L ≤ x
  · simp only [h, decide_true, Bool.toNat_true, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at he
    rw [ite_eq_left h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Ed25519.AArch64

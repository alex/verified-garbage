import VerifiedGarbage.Impl.Ed25519.X86_64.Scalar
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.X25519.X86_64.Small

/-!
# Ed25519 scalar reduction: one bit on x86-64

Untrusted. Carry and borrow equations account for every bit of all four
limbs. The final masked selection implements the conditional subtraction.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (val4 Keeps adc_carry chain_sub se0 toNat_ofBool mask xor_sel)
open VG.Spec.Ed25519 (L)

def scalarValue (s : State) : Nat := val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
def savedValue (s : State) : Nat := val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)

theorem val4_bound (a b c d : BitVec 64) : val4 a b c d < 2 ^ 256 := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [val4]; omega

theorem order_limbs : val4 orderLo orderHi 0 orderTop = L := by decide

theorem double_chain (a b c d : BitVec 64) (bit : Bool) :
    let c0 := decide (2 ^ 64 ≤ a.toNat + a.toNat + bit.toNat)
    let c1 := decide (2 ^ 64 ≤ b.toNat + b.toNat + c0.toNat)
    let c2 := decide (2 ^ 64 ≤ c.toNat + c.toNat + c1.toNat)
    let c3 := decide (2 ^ 64 ≤ d.toNat + d.toNat + c2.toNat)
    val4 (a + a + (BitVec.ofBool bit).setWidth 64)
      (b + b + (BitVec.ofBool c0).setWidth 64)
      (c + c + (BitVec.ofBool c1).setWidth 64)
      (d + d + (BitVec.ofBool c2).setWidth 64) + 2 ^ 256 * c3.toNat =
      2 * val4 a b c d + bit.toNat := by
  intro c0 c1 c2 c3
  have e0 := adc_carry a a bit
  have e1 := adc_carry b b c0
  have e2 := adc_carry c c c1
  have e3 := adc_carry d d c2
  dsimp only [c0, c1, c2, c3] at e1 e2 e3 ⊢
  simp only [val4]
  omega

theorem scalarShift_ok (s : State) (j : Nat) (hj : j < 8) (hr : scalarValue s < L) :
    WP isa (.block (scalarShift j)) s fun t =>
      scalarValue t = 2 * scalarValue s + ((s.gpr .rbp).getLsbD j).toNat ∧
      Keeps [.rcx, .r8, .r9, .r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [scalarShift, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    RegUpd.cf_setReg, RegUpd.cf_setFlags, RegUpd.cf_arithFlags,
    show 1 ≤ j + 1 ∧ j + 1 ≤ 63 by omega, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', Nat.add_sub_cancel, and_self]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := double_chain (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
      ((s.gpr .rbp).getLsbD j)
    have hb := Bool.toNat_le ((s.gpr .rbp).getLsbD j)
    have hL := order_bound
    simp only [scalarValue, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
      ite_true, ite_false, reduceCtorEq]
    simp only [scalarValue] at hr
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem subtract_chain (a b c d : BitVec 64) :
    let c0 := decide (a.toNat < orderLo.toNat)
    let c1 := decide (b.toNat < orderHi.toNat + c0.toNat)
    let c2 := decide (c.toNat < (0 : BitVec 64).toNat + c1.toNat)
    let c3 := decide (d.toNat < orderTop.toNat + c2.toNat)
    let v := val4 (a - orderLo) (b - orderHi - (BitVec.ofBool c0).setWidth 64)
      (c - 0 - (BitVec.ofBool c1).setWidth 64) (d - orderTop - (BitVec.ofBool c2).setWidth 64)
    c3 = decide (val4 a b c d < L) ∧
      v + L = val4 a b c d + 2 ^ 256 * c3.toNat := by
  intro c0 c1 c2 c3 v
  have e := chain_sub a b c d orderLo orderHi 0 orderTop
  change v + val4 orderLo orderHi 0 orderTop = val4 a b c d + 2 ^ 256 * c3.toNat at e
  rw [order_limbs] at e
  have hv : v < 2 ^ 256 := val4_bound _ _ _ _
  have hx := val4_bound a b c d
  clear_value v c3 c2 c1 c0
  refine ⟨?_, e⟩
  cases c3 <;> simp only [Bool.toNat_false, Bool.toNat_true] at e
  · exact (decide_eq_false (by omega)).symm
  · exact (decide_eq_true (by omega)).symm

theorem scalarSubtract_ok (s : State) :
    WP isa (.block scalarSubtract) s fun t =>
      t.cf = some (decide (scalarValue s < L)) ∧
      scalarValue t + L = scalarValue s + 2 ^ 256 * (decide (scalarValue s < L)).toNat ∧
      savedValue t = scalarValue s ∧
      Keeps [.rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  apply WP.of_runBlock
  simp only [scalarSubtract, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', se0]
  obtain ⟨hc, he⟩ := subtract_chain (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
  simp only [scalarValue, savedValue, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq]
  refine ⟨hc, ?_, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hc] at he; exact he
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem sbb_mask (x : BitVec 64) (b : Bool) :
    x - x - (BitVec.ofBool b).setWidth 64 = mask b := by
  rw [BitVec.sub_self]
  cases b <;> decide

theorem scalarSelect_ok (s : State) (borrow : Bool) (hc : s.cf = some borrow) :
    WP isa (.block scalarSelect) s fun t =>
      scalarValue t = (if borrow then savedValue s else scalarValue s) ∧
      Keeps [.rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  apply WP.of_runBlock
  simp only [scalarSelect, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hc,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', sbb_mask]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [scalarValue, savedValue, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      ite_true, ite_false, reduceCtorEq, (xor_sel borrow _ _).2]
    cases borrow <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

def scalarClob : List Reg := [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem select_remainder (x y : Nat) (hx : x < 2 * L)
    (he : y + L = x + 2 ^ 256 * (decide (x < L)).toNat) :
    (if x < L then x else y) = x % L := by
  by_cases h : x < L
  · rw [ite_eq_left h, Nat.mod_eq_of_lt h]
  · simp only [h, decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at he
    rw [ite_eq_right h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem scalarBit_ok (s : State) (j : Nat) (hj : j < 8) (hr : scalarValue s < L) :
    WP isa (.block (scalarBit j)) s fun t =>
      scalarValue t = (2 * scalarValue s + ((s.gpr .rbp).getLsbD j).toNat) % L ∧
      Keeps scalarClob s t := by
  rw [scalarBit, List.append_assoc, WP.block_append_iff]
  refine WP.mono (scalarShift_ok s j hj hr) fun t ⟨ht, kt⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarSubtract_ok t) fun u ⟨hc, hu, hsaved, ku⟩ => ?_
  refine WP.mono (scalarSelect_ok u _ hc) fun v ⟨hv, kv⟩ => ?_
  have b := Bool.toNat_le ((s.gpr .rbp).getLsbD j)
  have hx : scalarValue t < 2 * L := by omega
  have he := select_remainder (scalarValue t) (scalarValue u) hx hu
  have k1 : Keeps scalarClob s t := kt.mono (by simp [scalarClob])
  have k2 : Keeps scalarClob t u := ku.mono (by simp [scalarClob])
  have k3 : Keeps scalarClob u v := kv.mono (by simp [scalarClob])
  refine ⟨?_, k1.trans (k2.trans k3)⟩
  simp only [decide_eq_true_eq] at hv
  rw [hv, hsaved, he, ht]

end VG.Proof.Ed25519.X86_64

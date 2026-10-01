import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarStep
import VerifiedGarbage.Proof.Ed25519.ScalarWord

/-!
# Ed25519 scalar reduction: one word on AArch64

Untrusted. `wordFold` turns the remainder `r < L` and the next word `w` into
`l + L - h c` for `2^64 r + w = h 2^252 + l`, with `L = 2^252 + c`: below `2L`
and congruent to `2^64 r + w` modulo `L` (`fold_nat`). Each of its blocks is
checked against the numbers it computes.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64
open VG.Spec.Ed25519 (L)

theorem c_limbs : orderLo.toNat + 2 ^ 64 * orderHi.toNat = cL := by decide

theorem orderHi_lt : orderHi.toNat < 2 ^ 61 := by decide

theorem shr_or_shl (a b : Word) :
    (a >>> 60 ||| b <<< 4).toNat = a.toNat / 2 ^ 60 + 16 * (b.toNat % 2 ^ 60) := by
  have ha : a.toNat / 2 ^ 60 < 2 ^ 4 := by have := a.isLt; omega
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, show b.toNat * 2 ^ 4 % 2 ^ 64 = 16 * (b.toNat % 2 ^ 60) by omega]
  exact or_mul16 ha

theorem shl_shr (x : Word) : ((x <<< 4) >>> 4).toNat = x.toNat % 2 ^ 60 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem shr60 (x : Word) : (x >>> 60).toNat = x.toNat / 2 ^ 60 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem foldPrep_ok (s : State) :
    WP isa (.block foldPrep) s fun t =>
      (t.gpr .x12).toNat = (s.gpr .x6).toNat / 2 ^ 60 + 16 * ((s.gpr .x7).toNat % 2 ^ 60) ∧
      (t.gpr .x13).toNat = (s.gpr .x7).toNat / 2 ^ 60 ∧
      t.gpr .x4 = s.gpr .x3 ∧ t.gpr .x5 = s.gpr .x4 ∧ t.gpr .x6 = s.gpr .x5 ∧
      (t.gpr .x7).toNat = (s.gpr .x6).toNat % 2 ^ 60 ∧
      Keeps [.x12, .x13, .x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  simp only [foldPrep, mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 60 < Size.x.bits from by decide, show 4 < Size.x.bits from by decide,
    show (0 : Nat) < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨shr_or_shl _ _, shr60 _, trivial, trivial, trivial, shl_shr _, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2,
    ite_false]

theorem foldConst_ok (s : State) :
    WP isa (.block foldConst) s fun t =>
      t.gpr .x8 = orderLo ∧ t.gpr .x17 = orderHi ∧ Keeps [.x8, .x17] s t := by
  rw [foldConst, WP.block_append_iff]
  refine WP.mono (const64_ok s .x8 orderLo) fun a ⟨a8, ka⟩ => ?_
  refine WP.mono (const64_ok a .x17 orderHi) fun t ⟨t17, kt⟩ => ?_
  exact ⟨(kt.gpr .x8 (by decide)).trans a8, t17, (ka.mono (by decide)).trans (kt.mono (by decide))⟩

theorem umulh_toNat (a b : Word) :
    (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have hp : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' a.isLt b.isLt
  rw [BitVec.toNat_ofNat]
  omega

/-- `x (c₀ + 2^64 c₁)` from `mul`, `umulh` and one add with carry, for `c₁ < 2^61`. -/
theorem mul2_value (x c0 c1 : Word) (hc1 : c1.toNat < 2 ^ 61) :
    (x * c0).toNat +
        2 ^ 64 * (addCarry (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false).toNat +
        2 ^ 128 * (addCarry (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64)) 0
          (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false)).toNat =
      x.toNat * c0.toNat + 2 ^ 64 * (x.toNat * c1.toNat) := by
  have hp1 : x.toNat * c1.toNat < 2 ^ 64 * 2 ^ 61 := Nat.mul_lt_mul'' x.isLt hc1
  have hA := umulh_toNat x c0
  have hC := umulh_toNat x c1
  have hB := BitVec.toNat_mul x c1
  have hD := BitVec.toNat_mul x c0
  have e1 := addCarry_value (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false
  have e2 := addCarry_value (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64)) 0
    (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false)
  have hcy := Bool.toNat_le (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false)
  have hcy2 := Bool.toNat_le (carryOut (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64)) 0
    (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false))
  simp only [Bool.toNat_false, Nat.add_zero, show (0 : Word).toNat = 0 from rfl] at e1 e2
  omega

/-- A two-word sum that cannot carry out of its top word. -/
theorem add2_value (a0 a1 b0 b1 : Word) (h : a1.toNat + b1.toNat + 1 < 2 ^ 64) :
    (addCarry a0 b0 false).toNat + 2 ^ 64 * (addCarry a1 b1 (carryOut a0 b0 false)).toNat =
      a0.toNat + 2 ^ 64 * a1.toNat + (b0.toNat + 2 ^ 64 * b1.toNat) := by
  have e1 := addCarry_value a0 b0 false
  have e2 := addCarry_value a1 b1 (carryOut a0 b0 false)
  have hcy := Bool.toNat_le (carryOut a0 b0 false)
  have hcy2 := Bool.toNat_le (carryOut a1 b1 (carryOut a0 b0 false))
  simp only [Bool.toNat_false, Nat.add_zero] at e1
  omega

theorem foldMul_ok (s : State) (h8 : s.gpr .x8 = orderLo) (h17 : s.gpr .x17 = orderHi)
    (hz : s.gpr .x10 = 0) :
    WP isa (.block foldMul) s fun t =>
      (t.gpr .x14).toNat + 2 ^ 64 * (t.gpr .x15).toNat + 2 ^ 128 * (t.gpr .x16).toNat =
        (s.gpr .x12).toNat * cL ∧ Keeps [.x9, .x14, .x15, .x16] s t := by
  apply WP.of_runBlock
  simp only [foldMul, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h8, h17, hz, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have hc : (s.gpr .x12).toNat * cL =
        (s.gpr .x12).toNat * orderLo.toNat + 2 ^ 64 * ((s.gpr .x12).toNat * orderHi.toNat) := by
      rw [← c_limbs, Nat.mul_add, Nat.mul_left_comm]
    have H := mul2_value (s.gpr .x12) orderLo orderHi orderHi_lt
    dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    rw [hc]
    exact H
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

theorem mul_bit (h v : Word) (hh : h.toNat ≤ 1) : (h * v).toNat = h.toNat * v.toNat := by
  rw [BitVec.toNat_mul]
  rcases (by omega : h.toNat = 0 ∨ h.toNat = 1) with e | e <;> rw [e]
  · rw [Nat.zero_mul, Nat.zero_mod]
  · rw [Nat.one_mul]; exact Nat.mod_eq_of_lt v.isLt

theorem foldHigh_ok (s : State) (h8 : s.gpr .x8 = orderLo) (h17 : s.gpr .x17 = orderHi)
    (h1 : (s.gpr .x13).toNat ≤ 1) (h16 : (s.gpr .x16).toNat < 2 ^ 62) :
    WP isa (.block foldHigh) s fun t => t.gpr .x14 = s.gpr .x14 ∧
      (t.gpr .x15).toNat + 2 ^ 64 * (t.gpr .x16).toNat =
        (s.gpr .x15).toNat + 2 ^ 64 * (s.gpr .x16).toNat + (s.gpr .x13).toNat * cL ∧
      Keeps [.x9, .x13, .x15, .x16] s t := by
  apply WP.of_runBlock
  simp only [foldHigh, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h8, h17, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have mx := mul_bit (s.gpr .x13) orderLo h1
    have my := mul_bit (s.gpr .x13) orderHi h1
    have hc : (s.gpr .x13).toNat * cL =
        (s.gpr .x13).toNat * orderLo.toNat + 2 ^ 64 * ((s.gpr .x13).toNat * orderHi.toNat) := by
      rw [← c_limbs, Nat.mul_add, Nat.mul_left_comm]
    have hy : (s.gpr .x13).toNat * orderHi.toNat < 2 ^ 61 := by
      have := orderHi_lt
      rcases (by omega : (s.gpr .x13).toNat = 0 ∨ (s.gpr .x13).toNat = 1) with e | e <;>
        rw [e] <;> omega
    have H := add2_value (s.gpr .x15) (s.gpr .x16) (s.gpr .x13 * orderLo) (s.gpr .x13 * orderHi)
      (by rw [my]; omega)
    dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    rw [H, mx, my, hc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

theorem orderTop_movz : (0x1000 : BitVec 16).setWidth 64 <<< (16 * 3) = orderTop := by decide

theorem foldSub_ok (s : State) (h8 : s.gpr .x8 = orderLo) (h17 : s.gpr .x17 = orderHi)
    (hz : s.gpr .x10 = 0)
    (ht : (s.gpr .x14).toNat + 2 ^ 64 * (s.gpr .x15).toNat + 2 ^ 128 * (s.gpr .x16).toNat < L) :
    WP isa (.block foldSub) s fun t =>
      val4 (t.gpr .x14) (t.gpr .x15) (t.gpr .x16) (t.gpr .x9) =
        L - ((s.gpr .x14).toNat + 2 ^ 64 * (s.gpr .x15).toNat + 2 ^ 128 * (s.gpr .x16).toNat) ∧
      Keeps [.x9, .x14, .x15, .x16] s t := by
  apply WP.of_runBlock
  simp only [foldSub, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 3 < Size.x.bits from by decide,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_write, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h8, h17, hz, orderTop_movz, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := sub4_value orderLo orderHi 0 orderTop (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) 0 true
    simp only [order_limbs, Bool.toNat_true, Nat.sub_self, Nat.add_zero] at e
    have hT : val4 (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) 0 =
        (s.gpr .x14).toNat + 2 ^ 64 * (s.gpr .x15).toNat + 2 ^ 128 * (s.gpr .x16).toNat := by
      simp only [val4, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    rw [hT] at e
    dsimp only [addCarry, carryOut, Size.bits] at e ⊢
    exact eq_sub_of_chain (val4_lt _ _ _ _) ht e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

theorem foldAdd_ok (s : State)
    (hs : scalarValue s + val4 (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x9) < 2 ^ 256) :
    WP isa (.block foldAdd) s fun t =>
      scalarValue t = scalarValue s + val4 (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x9) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  simp only [foldAdd, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := add4_value (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
      (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x9) false
    simp only [Bool.toNat_false, Nat.add_zero] at e
    dsimp only [addCarry, carryOut, Size.bits, scalarValue] at e hs ⊢
    exact eq_of_chain hs e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The registers `wordFold` changes. -/
def foldClob : List Reg := [.x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17]

theorem wordFold_ok (s : State) (hr : scalarValue s < L) (hz : s.gpr .x10 = 0) :
    WP isa (.block wordFold) s fun t => scalarValue t < 2 * L ∧
      scalarValue t % L = (scalarValue s * 2 ^ 64 + (s.gpr .x3).toNat) % L ∧
      Keeps foldClob s t := by
  have hw := (s.gpr .x3).isLt
  obtain ⟨hlt, hlt2, hmod⟩ := fold_nat (scalarValue s) (s.gpr .x3).toNat hr hw
  have h0 := (s.gpr .x4).isLt; have h1 := (s.gpr .x5).isLt; have h2 := (s.gpr .x6).isLt
  have h3 : (s.gpr .x7).toNat < 2 ^ 61 := by
    have hL : L < 2 ^ 253 := by decide
    have := hr; simp only [scalarValue, val4] at this; omega
  have eh : (scalarValue s * 2 ^ 64 + (s.gpr .x3).toNat) / 2 ^ 252 =
      ((s.gpr .x6).toNat / 2 ^ 60 + 16 * ((s.gpr .x7).toNat % 2 ^ 60)) +
        2 ^ 64 * ((s.gpr .x7).toNat / 2 ^ 60) := by
    simp only [scalarValue, val4]; omega
  have el : (scalarValue s * 2 ^ 64 + (s.gpr .x3).toNat) % 2 ^ 252 =
      (s.gpr .x3).toNat + 2 ^ 64 * (s.gpr .x4).toNat + 2 ^ 128 * (s.gpr .x5).toNat +
        2 ^ 192 * ((s.gpr .x6).toNat % 2 ^ 60) := by
    simp only [scalarValue, val4]; omega
  rw [eh] at hlt hlt2 hmod
  rw [el] at hlt2 hmod
  simp only [wordFold, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (foldPrep_ok s) fun a ⟨a12, a13, a4, a5, a6, a7, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (foldConst_ok a) fun b ⟨b8, b17, kb⟩ => ?_
  have hzb : b.gpr .x10 = 0 := by
    rw [kb.gpr .x10 (by decide), ka.gpr .x10 (by decide)]; exact hz
  rw [WP.block_append_iff]
  refine WP.mono (foldMul_ok b b8 b17 hzb) fun c ⟨ct, kc⟩ => ?_
  have c13 : c.gpr .x13 = a.gpr .x13 := by
    rw [kc.gpr .x13 (by decide), kb.gpr .x13 (by decide)]
  have c12 : c.gpr .x12 = a.gpr .x12 := by
    rw [kc.gpr .x12 (by decide), kb.gpr .x12 (by decide)]
  have hb1 : (c.gpr .x13).toNat ≤ 1 := by rw [c13, a13]; omega
  have hb16 : (c.gpr .x16).toNat < 2 ^ 62 := by
    have : (b.gpr .x12).toNat * cL < 2 ^ 64 * cL :=
      Nat.mul_lt_mul_of_pos_right (b.gpr .x12).isLt (by decide)
    simp only [cL] at this ct; omega
  rw [WP.block_append_iff]
  refine WP.mono (foldHigh_ok c ((kc.gpr .x8 (by decide)).trans b8)
    ((kc.gpr .x17 (by decide)).trans b17) hb1 hb16) fun d ⟨d14, dt, kd⟩ => ?_
  have hT : (d.gpr .x14).toNat + 2 ^ 64 * (d.gpr .x15).toNat + 2 ^ 128 * (d.gpr .x16).toNat =
      ((s.gpr .x6).toNat / 2 ^ 60 + 16 * ((s.gpr .x7).toNat % 2 ^ 60) +
        2 ^ 64 * ((s.gpr .x7).toNat / 2 ^ 60)) * cL := by
    have b12 : b.gpr .x12 = a.gpr .x12 := kb.gpr .x12 (by decide)
    rw [d14, Nat.add_mul, ← a12, ← a13, ← c13, ← b12, Nat.mul_assoc]
    omega
  have d8 : d.gpr .x8 = orderLo := by
    rw [kd.gpr .x8 (by decide), kc.gpr .x8 (by decide)]; exact b8
  have d17 : d.gpr .x17 = orderHi := by
    rw [kd.gpr .x17 (by decide), kc.gpr .x17 (by decide)]; exact b17
  have dz : d.gpr .x10 = 0 := by
    rw [kd.gpr .x10 (by decide), kc.gpr .x10 (by decide)]; exact hzb
  rw [WP.block_append_iff]
  refine WP.mono (foldSub_ok d d8 d17 dz (by rw [hT]; exact hlt)) fun e ⟨eu, ke⟩ => ?_
  have hl : scalarValue e = (s.gpr .x3).toNat + 2 ^ 64 * (s.gpr .x4).toNat +
      2 ^ 128 * (s.gpr .x5).toNat + 2 ^ 192 * ((s.gpr .x6).toNat % 2 ^ 60) := by
    simp only [scalarValue, val4]
    rw [ke.gpr .x4 (by decide), ke.gpr .x5 (by decide), ke.gpr .x6 (by decide),
      ke.gpr .x7 (by decide), kd.gpr .x4 (by decide), kd.gpr .x5 (by decide),
      kd.gpr .x6 (by decide), kd.gpr .x7 (by decide), kc.gpr .x4 (by decide),
      kc.gpr .x5 (by decide), kc.gpr .x6 (by decide), kc.gpr .x7 (by decide),
      kb.gpr .x4 (by decide), kb.gpr .x5 (by decide), kb.gpr .x6 (by decide),
      kb.gpr .x7 (by decide), a4, a5, a6, a7]
  rw [hT] at eu
  refine WP.mono (foldAdd_ok e (by rw [hl, eu]; have := order_bound; omega)) fun t ⟨tv, kt⟩ => ?_
  refine ⟨by rw [tv, hl, eu]; exact hlt2, by rw [tv, hl, eu]; exact hmod, ?_⟩
  exact ((((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    ((kc.mono (by decide)).trans (kd.mono (by decide)))).trans (ke.mono (by decide))).trans
    (kt.mono (by decide))

end VG.Proof.Ed25519.AArch64

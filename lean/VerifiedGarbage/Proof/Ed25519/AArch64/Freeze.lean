import VerifiedGarbage.Proof.Ed25519.AArch64.Ops
import VerifiedGarbage.Proof.Ed25519.Canonical64

/-! Full reduction of four limbs to the canonical residue. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64
open VG.Spec.X25519 (P)

theorem freezeFold_ok (s : State) (hz : s.gpr .x10 = 0) (h19 : s.gpr .x11 = 19)
    (hl : s.gpr .x2 = low63) :
    WP isa (.block freezeFold) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) % P =
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % P ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) < 2 ^ 255 + 19 ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x3] s t := by
  have hm (x : Word) : ((x >>> 63) * 19).toNat = 19 * (x.toNat / 2 ^ 63) := by
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show (19 : Word).toNat = 19 from rfl, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
  apply WP.of_runBlock
  simp only [freezeFold, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, hz, h19, hl, show 63 < Size.x.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have H := fold_top (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
    (s.gpr .x7 &&& low63) ((s.gpr .x7 >>> 63) * 19) (hm _) (and_low63 _)
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem freezeCandidate_ok (s : State) (hz : s.gpr .x10 = 0) (h19 : s.gpr .x11 = 19)
    (hl : s.gpr .x2 = low63)
    (hx : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) < 2 ^ 255 + 19) :
    WP isa (.block freezeCandidate) s fun t =>
      t.gpr .x3 = mask (decide (P ≤ val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7))) ∧
      (P ≤ val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) →
        val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) =
          val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) - P) ∧
      Keeps [.x21, .x22, .x23, .x24, .x8, .x3] s t := by
  apply WP.of_runBlock
  simp only [freezeCandidate, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, hz, h19, hl, show 63 < Size.x.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have H := add19_top (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) hx
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits, low63] at H ⊢
    exact H.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem select4_ok (s : State) {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block select4) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        (if sw then val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)
          else val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) ∧
      Keeps [.x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [select4, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, hm, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', xor_sel']
  refine ⟨by cases sw <;> rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

/-- The result is the unique representative below p. -/
theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : FieldRange a) :
    WP isa (.block (freeze a)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem base a % P ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x21, .x22, .x23, .x24] s t := by
  rw [freeze, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (fieldInit_ok s 19) fun s₀ ⟨hz, h19, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₀ .x2 low63) fun s₁ ⟨hl, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs₁ ha (by decide)) fun s₂ ⟨w4, w5, w6, w7, k2⟩ => ?_
  have hz2 : s₂.gpr .x10 = 0 := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans hz)
  have h192 : s₂.gpr .x11 = 19 := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h19)
  have hl2 : s₂.gpr .x2 = low63 := (k2.gpr _ (by decide)).trans hl
  rw [WP.block_append_iff]
  refine WP.mono (freezeFold_ok s₂ hz2 h192 hl2) fun s₃ ⟨e3, b3, k3⟩ => ?_
  have hz3 := (k3.gpr .x10 (by decide)).trans hz2
  have h193 := (k3.gpr .x11 (by decide)).trans h192
  have hl3 := (k3.gpr .x2 (by decide)).trans hl2
  rw [WP.block_append_iff]
  refine WP.mono (freezeCandidate_ok s₃ hz3 h193 hl3 b3) fun s₄ ⟨m4, v4, k4⟩ => ?_
  refine WP.mono (select4_ok s₄ m4) fun s₅ ⟨v5, k5⟩ => ?_
  have K : Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x21, .x22, .x23, .x24] s s₅ :=
    ((((k0.mono (by decide)).trans (k1.mono (by decide))).trans (k2.mono (by decide))).trans
      (k3.mono (by decide))).trans (k4.mono (by decide)) |>.trans (k5.mono (by decide))
  rw [k4.gpr .x4 (by decide), k4.gpr .x5 (by decide), k4.gpr .x6 (by decide),
    k4.gpr .x7 (by decide)] at v5
  rw [w4, w5, w6, w7, k1.mem, k0.mem] at e3
  refine ⟨?_, K⟩
  rw [v5, ← e3]
  generalize val4 (s₃.gpr .x4) (s₃.gpr .x5) (s₃.gpr .x6) (s₃.gpr .x7) = x at b3 v4 ⊢
  by_cases h : P ≤ x
  · simp only [decide_eq_true h, ite_true]
    rw [v4 h]
    simp only [P] at h b3 ⊢
    omega_using [h, b3]
  · simp only [decide_eq_false h, Bool.false_eq_true, ite_false]
    exact (Nat.mod_eq_of_lt (by omega)).symm

end VG.Proof.Ed25519.AArch64

import VerifiedGarbage.Proof.Ed25519.AArch64.Ops
import VerifiedGarbage.Proof.Ed25519.Canonical64

/-! Untrusted: swapping four limbs with a mask and writing the two field elements. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

theorem swapWords_ok (s : State) (sw : Bool) (hm : s.gpr .x3 = mask sw) :
    WP isa (.block swapWords) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        (if sw then val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)
          else val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) ∧
      val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) =
        (if sw then val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
          else val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [swapWords, swapWord, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', hm, (xor_sel sw _ _).1, (xor_sel sw _ _).2]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · cases sw <;> rfl
  · cases sw <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem cswap_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat}
    (hx : FieldRange x) (hy : FieldRange y) (hxy : x + 32 ≤ y ∨ y + 32 ≤ x)
    {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block (cswap x y)) s fun t =>
      (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧ t.gpr .x3 = s.gpr .x3 ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∃ m, Outside base x 32 s.mem m ∧ Outside base y 32 m t.mem ∧
        fe m base x = if sw then fe s.mem base y else fe s.mem base x) ∧
      fe t.mem base x = (if sw then fe s.mem base y else fe s.mem base x) ∧
      fe t.mem base y = (if sw then fe s.mem base x else fe s.mem base y) := by
  rw [cswap, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs hx (by decide)) fun s₁ ⟨a0, a1, a2, a3, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (hs.of_keeps k1 (by decide)) hy (by decide)) fun s₂ ⟨b0, b1, b2, b3, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (swapWords_ok s₂ sw (by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), hm]))
    fun s₃ ⟨v3, w3, k3⟩ => ?_
  have va : val4 (s₂.gpr .x4) (s₂.gpr .x5) (s₂.gpr .x6) (s₂.gpr .x7) = fe s.mem base x := by
    rw [k2.gpr _ (by decide), k2.gpr _ (by decide), k2.gpr _ (by decide), k2.gpr _ (by decide),
      a0, a1, a2, a3]
  have vb : val4 (s₂.gpr .x21) (s₂.gpr .x22) (s₂.gpr .x23) (s₂.gpr .x24) = fe s.mem base y := by
    rw [b0, b1, b2, b3, k1.mem]
  rw [va, vb] at v3 w3
  have hs₃ := (hs.of_keeps k1 (by decide)).of_keeps k2 (by decide) |>.of_keeps k3 (by decide)
  have K : Keeps clob s s₃ := ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))
  have hc : s₃.gpr .x3 = s.gpr .x3 := by
    rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok hs₃ hx) fun s₄ h4 => ?_
  subst s₄
  refine WP.mono (stores_ok (hs₃.setMem _) hy .x21 .x22 .x23 .x24) fun t ht => ?_
  subst t
  have o1 := st4_outside s₃.mem base (show x + 32 < 2 ^ 64 by have := hx.2; omega)
    (s₃.gpr .x4) (s₃.gpr .x5) (s₃.gpr .x6) (s₃.gpr .x7)
  have o2 := st4_outside (st4 s₃.mem base x (s₃.gpr .x4) (s₃.gpr .x5) (s₃.gpr .x6) (s₃.gpr .x7))
    base (show y + 32 < 2 ^ 64 by have := hy.2; omega)
    (s₃.gpr .x21) (s₃.gpr .x22) (s₃.gpr .x23) (s₃.gpr .x24)
  have vx : fe (st4 s₃.mem base x (s₃.gpr .x4) (s₃.gpr .x5) (s₃.gpr .x6) (s₃.gpr .x7)) base x =
      if sw then fe s.mem base y else fe s.mem base x := by
    rw [fe_st4 _ _ (by have := hx.2; omega)]; exact v3
  refine ⟨K.gpr, hc, K.rd, K.wr, K.sp, ⟨_, ?_, o2, vx⟩, ?_, ?_⟩
  · rw [← K.mem]; exact o1
  · rw [o2.fe hxy (by have := hx.2; omega)]; exact vx
  · rw [fe_st4 _ _ (by have := hy.2; omega)]; exact w3

end VG.Proof.Ed25519.AArch64

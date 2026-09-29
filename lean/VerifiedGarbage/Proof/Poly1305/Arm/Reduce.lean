import VerifiedGarbage.Proof.Poly1305.Arm.Carry
import Mathlib.Tactic.IntervalCases

/-!
# Poly1305 on 32-bit ARM: carrying all columns, the final reduction, and words

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

theorem Cols.keep {v : Nat → Nat} {s s' : State} (h : Cols v s) {ws : List Reg} (hk : Keeps ws s s')
    (hw : ∀ j < 10, yr j ∉ ws) : Cols v s' := fun j hj => by rw [hk.gpr _ (hw j hj)]; exact h j hj

theorem carryFold_ok {f : Nat → Nat} (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) {s : State} (hc : Cols f s) :
    WP isa (.block carryFold) s fun s' =>
      Cols (fold f) s' ∧ s'.gpr .r2 = maskV ∧ Keeps (.r2 :: .r12 :: cregs) s s' := by
  rw [carryFold, List.cons_append, List.cons_append]
  refine wp_movw fun s1 u1 => ?_
  have hc1 : Cols f s1 := hc.keep (u1.keeps (List.mem_singleton_self _)) fun j hj => by
    simpa using (yr_ne' j hj).2.1
  rw [List.append_assoc]
  refine WP.append (carries_ok 0 9 (by omega) hf hc1 u1.gpr) fun s2 ⟨hc2, k2⟩ => ?_
  have hl := fun j (hj : j < 9) => carryN_lt f 0 9 j (by omega) (by omega)
  have hF9 := hc2 9 (by omega)
  have hF0 := hc2 0 (by omega)
  have hF1 := hc2 1 (by omega)
  simp only [yr] at hF9 hF0 hF1
  have hm2 : s2.gpr .r2 = maskV := by rw [k2.gpr _ cregs_r2, u1.gpr]; rfl
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr (by omega)) fun s3 u3 => wp_and (op2_reg _ _) fun s4 u4 => ?_
  refine wp_add (op2_lsl (by omega)) fun s5 u5 => wp_add (op2_reg _ _) fun s6 u6 => ?_
  -- The values of `r12`, `r1` and `r3`.
  have hc9 : (s3.gpr .r12).toNat = carryN f 0 9 9 / 2 ^ 13 := by rw [u3.gpr, toNat_shr, hF9]
  have hc9' : carryN f 0 9 9 / 2 ^ 13 < 2 ^ 19 := by have := (s2.gpr .r1).isLt; omega
  have h12 : (s5.gpr .r12).toNat = 5 * (carryN f 0 9 9 / 2 ^ 13) := by
    rw [u5.gpr, u4.other _ (by decide), toNat_add_lt (by rw [toNat_shl]; omega), toNat_shl, hc9]
    omega
  have h1 : (s6.gpr .r1).toNat = carryN f 0 9 9 % 2 ^ 13 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.other _ (by decide),
      u3.other _ (by decide), hm2, toNat_and_mask, hF9]
  have h3 : (s6.gpr .r3).toNat = carryN f 0 9 0 + 5 * (carryN f 0 9 9 / 2 ^ 13) := by
    have := hl 0 (by omega)
    rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      toNat_add_lt (by rw [h12, hF0]; omega), h12, hF0]
  have h4 : (s6.gpr .r4).toNat = carryN f 0 9 1 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), hF1]
  have hm6 : s6.gpr .r2 = maskV := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), hm2]
  have hk6 : Keeps (.r2 :: .r12 :: cregs) s s6 :=
    (u1.keeps (by simp)).trans ((k2.mono fun r hr => by simp [hr]).trans ((u3.keeps (by simp)).trans
      ((u4.keeps (by simp [cregs])).trans ((u5.keeps (by simp)).trans (u6.keeps (by simp [cregs, yregs]))))))
  refine WP.mono (carryStep_ok (k := 0) (by omega) hm6 (by
    simp only [yr, Nat.zero_add]; rw [h3, h4]; have := hl 1 (by omega); omega))
    fun s7 ⟨e1, e0, k7⟩ => ⟨fun j hj => ?_, ?_, hk6.trans (k7.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [yr, cregs, yregs])⟩
  · simp only [Nat.zero_add] at e1 e0
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j
      · rw [e0, fold_0]; simp only [yr] at h3 ⊢; rw [h3]
      · rw [e1, fold_1]; simp only [yr] at h3 h4 ⊢; rw [h3, h4]
    have k26 : Keeps [.r12, .r1, .r3] s2 s6 :=
      (u3.keeps (by simp)).trans ((u4.keeps (by simp)).trans ((u5.keeps (by simp)).trans
        (u6.keeps (by simp))))
    rcases Nat.lt_or_ge j 9 with h' | h'
    · have hn : ∀ j < 9, 2 ≤ j → yr j ∉ [Reg.r12, .r1, .r3] ∧ yr j ∉ [yr 0, yr (0 + 1)] := by decide
      rw [k7.gpr _ (hn j h' h).2, k26.gpr _ (hn j h' h).1, fold_mid f h h']
      exact hc2 j hj
    · rw [show j = 9 by omega, k7.gpr _ (by decide), fold_9]; exact h1
  · rw [k7.gpr _ (by simp [yr]), hm6]

theorem plus5_ok {K : Nat → Nat} (hK : ∀ j < 10, K j ≤ 2 ^ 13) {s : State} (hc : Cols K s) :
    WP isa (.block plus5) s fun s' => (s'.gpr .r12).toNat = chainT K 9 ∧ Keeps [.r12] s s' := by
  rw [plus5]
  refine wp_add (op2_imm (by decide)) fun s1 u1 => ?_
  have h0 := hc 0 (by omega)
  have hK0 := hK 0 (by omega)
  simp only [yr] at h0
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => (s'.gpr .r12).toNat = chainT K k ∧ Keeps [.r12] s1 s')
    (fun k s' hk ⟨h12, hk'⟩ => ?_) 9 (Nat.le_refl _) s1
    ⟨by rw [u1.gpr, toNat_add_lt (by rw [h0]; simp; omega), h0]; rfl, Keeps.refl _ _⟩)
    fun s' ⟨h, k⟩ => ⟨h, (u1.keeps (by simp)).trans k⟩
  have hy : (s'.gpr (yr (k + 1))).toNat = K (k + 1) := by
    rw [hk'.gpr _ (by have := (yr_ne' (k + 1) (by omega)).2.2; simpa using this),
      u1.other _ (yr_ne' (k + 1) (by omega)).2.2]
    exact hc (k + 1) (by omega)
  have hle := chainT_le K hK k (by omega)
  have hle' := hK (k + 1) (by omega)
  refine wp_add (op2_lsr (by omega)) fun s2 u2 => WP.block_nil ⟨?_, hk'.trans (u2.keeps (by simp))⟩
  rw [u2.gpr, toNat_add_lt (by rw [toNat_shr, hy, h12]; omega), toNat_shr, hy, h12]
  rfl

theorem addC_ok {s : State} {t k0 : Nat} (ht : (s.gpr .r12).toNat = t) (ht' : t < 2 ^ 20)
    (h3 : (s.gpr .r3).toNat = k0) (hk0 : k0 < 2 ^ 20) :
    WP isa (.block addC) s fun s' => (s'.gpr .r3).toNat = k0 + 5 * (t / 2 ^ 13) ∧
      Keeps [.r12, .r3] s s' := by
  rw [addC]
  refine wp_mov (op2_lsr (by omega)) fun s1 u1 => wp_add (op2_lsl (by omega)) fun s2 u2 => ?_
  refine wp_add (op2_reg _ _) fun s3 u3 => WP.block_nil ⟨?_, (u1.keeps (by simp)).trans
    ((u2.keeps (by simp)).trans (u3.keeps (by simp)))⟩
  have e1 : (s1.gpr .r12).toNat = t / 2 ^ 13 := by rw [u1.gpr, toNat_shr, ht]
  have e2 : (s2.gpr .r12).toNat = 5 * (t / 2 ^ 13) := by
    rw [u2.gpr, toNat_add_lt (by rw [toNat_shl, e1]; omega), toNat_shl, e1]; omega
  rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide),
    toNat_add_lt (by rw [h3, e2]; omega), h3, e2]

theorem reduceRegs_ok {E : Nat → Nat} (hE : ∀ j < 10, E j < 2 ^ 32 - 2 ^ 19) {s : State}
    (hc : Cols E s) :
    WP isa (.block reduceRegs) s fun s' =>
      Cols (redL E) s' ∧ s'.gpr .r2 = maskV ∧ Keeps (.r2 :: .r12 :: cregs) s s' := by
  obtain ⟨hH, hK, hK', -, -⟩ := red_facts E hE
  rw [reduceRegs]
  simp only [List.append_assoc]
  refine WP.append (carryFold_ok hE hc) fun s1 ⟨hc1, hm1, k1⟩ => ?_
  refine WP.append (carries_ok 1 8 (by omega) hH hc1 hm1) fun s2 ⟨hc2, k2⟩ => ?_
  refine WP.append (plus5_ok hK hc2) fun s3 ⟨h12, k3⟩ => ?_
  have hc3 : Cols (redK E) s3 := hc2.keep k3 fun j hj => by simpa using (yr_ne' j hj).2.2
  have ht : chainT (redK E) 9 < 2 ^ 20 := by have := chainT_le _ hK 9 (by omega); omega
  have h30 : (s3.gpr .r3).toNat = redK E 0 := hc3 0 (by omega)
  have hk0 := hK 0 (by omega)
  refine WP.append (addC_ok h12 ht h30 (by omega)) fun s4 ⟨h4, k4⟩ => ?_
  have hc4 : Cols (redK' E) s4 := fun j hj => by
    simp only [redK']
    split
    · rename_i e; subst e; show (s4.gpr .r3).toNat = _; rw [h4, chainT_top]; rfl
    · rw [k4.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨(yr_ne' j hj).2.2, fun e => by have := yr_inj _ hj 0 (by omega) e; omega⟩)]
      exact hc3 j hj
  have hm4 : s4.gpr .r2 = maskV := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ cregs_r2, hm1]
  rw [carry3]
  refine WP.append (carries_ok 0 9 (by omega) hK' hc4 hm4) fun s5 ⟨hc5, k5⟩ => ?_
  have hm5 : s5.gpr .r2 = maskV := by rw [k5.gpr _ cregs_r2, hm4]
  refine wp_and (op2_reg _ _) fun s6 u6 => WP.block_nil ⟨fun j hj => ?_, ?_, ?_⟩
  · simp only [redL]
    split
    · rename_i e; subst e
      have := hc5 9 (by omega)
      simp only [yr] at this ⊢
      rw [u6.gpr, hm5, toNat_and_mask, this]
    · rw [u6.other _ (fun e => by have := yr_inj _ hj 9 (by omega) e; omega)]
      exact hc5 j hj
  · rw [u6.other _ (by decide), hm5]
  · refine k1.trans ((k2.mono fun r hr => by simp [hr]).trans ((k3.mono (by simp)).trans
      ((k4.mono (by simp [cregs, yregs])).trans ((k5.mono fun r hr => by simp [hr]).trans
        (u6.keeps (by simp [cregs]))))))

/-- The words of the limbs `L` (see `val_toWords`). -/
def tw0 (L : Nat → Nat) : Nat := L 0 + 2 ^ 13 * L 1 + 2 ^ 26 * (L 2 % 2 ^ 6)
def tw1 (L : Nat → Nat) : Nat := L 2 / 2 ^ 6 + 2 ^ 7 * L 3 + 2 ^ 20 * (L 4 % 2 ^ 12)
def tw2 (L : Nat → Nat) : Nat := L 4 / 2 ^ 12 + 2 * L 5 + 2 ^ 14 * L 6 + 2 ^ 27 * (L 7 % 2 ^ 5)
def tw3 (L : Nat → Nat) : Nat := L 7 / 2 ^ 5 + 2 ^ 8 * L 8 + 2 ^ 21 * (L 9 % 2 ^ 11)

theorem add_shl {x y : BitVec 32} {a : Nat} (h : x.toNat + y.toNat * 2 ^ a % 2 ^ 32 < 2 ^ 32) :
    (x + y <<< a).toNat = x.toNat + y.toNat * 2 ^ a % 2 ^ 32 := by
  rw [toNat_add_lt (by rw [toNat_shl]; exact h), toNat_shl]

theorem toWords_ok {L : Nat → Nat} {s : State} (hc : Cols L s) (hL : ∀ j < 9, L j < 2 ^ 13) :
    WP isa (.block toWords) s fun s' =>
      (s'.gpr .r3).toNat = tw0 L ∧ (s'.gpr .r5).toNat = tw1 L ∧ (s'.gpr .r7).toNat = tw2 L ∧
      (s'.gpr .r10).toNat = tw3 L ∧ (s'.gpr .r1).toNat = L 9 / 2 ^ 11 ∧
      Keeps [.r1, .r3, .r5, .r7, .r10] s s' := by
  have c0 := hc 0 (by omega); have c1 := hc 1 (by omega); have c2 := hc 2 (by omega)
  have c3 := hc 3 (by omega); have c4 := hc 4 (by omega); have c5 := hc 5 (by omega)
  have c6 := hc 6 (by omega); have c7 := hc 7 (by omega); have c8 := hc 8 (by omega)
  have c9 := hc 9 (by omega)
  simp only [yr] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  have l0 := hL 0 (by omega); have l1 := hL 1 (by omega); have l2 := hL 2 (by omega)
  have l3 := hL 3 (by omega); have l4 := hL 4 (by omega); have l5 := hL 5 (by omega)
  have l6 := hL 6 (by omega); have l7 := hL 7 (by omega); have l8 := hL 8 (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [toWords, runBlock_cons, runStep_some, runBlock_nil, exec,
    Op2.eval, isa, State.setReg, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [add_shl (by rw [add_shl (by omega)]; omega), add_shl (by omega), c0, c1, c2, tw0]; omega
  · rw [add_shl (by rw [add_shl (by rw [toNat_shr]; omega), toNat_shr]; omega),
      add_shl (by rw [toNat_shr]; omega), toNat_shr, c2, c3, c4, tw1]; omega
  · rw [add_shl (by rw [add_shl (by rw [add_shl (by rw [toNat_shr]; omega), toNat_shr]; omega),
      add_shl (by rw [toNat_shr]; omega), toNat_shr]; omega),
      add_shl (by rw [add_shl (by rw [toNat_shr]; omega), toNat_shr]; omega),
      add_shl (by rw [toNat_shr]; omega), toNat_shr, c4, c5, c6, c7, tw2]; omega
  · rw [add_shl (by rw [add_shl (by rw [toNat_shr]; omega), toNat_shr]; omega),
      add_shl (by rw [toNat_shr]; omega), toNat_shr, c7, c8, c9, tw3]; omega
  · rw [toNat_shr, c9]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h3, h5, h7, h10⟩ := hr
    simp [h1, h3, h5, h7, h10]

end VG.Proof.Poly1305.Arm

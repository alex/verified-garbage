import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Setup

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

/-- ZIP's word arrangement, without widening and narrowing its lanes. -/
theorem zip1_s4 (x y : BitVec 128) :
    VPermOp.eval .zip1 .s4 x y = ofVWords (vword x 0) (vword y 0) (vword x 1) (vword y 1) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.range_succ, List.getD]

theorem zip2_s4 (x y : BitVec 128) :
    VPermOp.eval .zip2 .s4 x y = ofVWords (vword x 2) (vword y 2) (vword x 3) (vword y 3) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.range_succ, List.getD]

theorem zip1_d2 (x y : BitVec 128) :
    VPermOp.eval .zip1 .d2 x y = ofVWords (vword x 0) (vword x 1) (vword y 0) (vword y 1) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.range_succ, List.getD]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofVDwords, ofVWords, vdword, vword, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  simp only [Nat.reduceMul, Nat.zero_add]
  by_cases h : i < 64
  · by_cases h' : i < 32
    · simp (disch := omega) only [ite_eq_left, decide_eq_true, Bool.true_and]
    · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega
  · by_cases h' : i < 96
    · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega
    · simp (disch := omega) only [ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega

theorem zip2_d2 (x y : BitVec 128) :
    VPermOp.eval .zip2 .d2 x y = ofVWords (vword x 2) (vword x 3) (vword y 2) (vword y 3) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.range_succ, List.getD]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofVDwords, ofVWords, vdword, vword, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  simp only [Nat.reduceMul]
  by_cases h : i < 64
  · by_cases h' : i < 32
    · simp (disch := omega) only [ite_eq_left, decide_eq_true, Bool.true_and]
    · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega
  · by_cases h' : i < 96
    · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega
    · simp (disch := omega) only [ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega

theorem rowWord_inj (r i j : Fin 4) : rowWord r i = rowWord r j ↔ i = j := by
  simp only [rowWord, Fin.ext_iff]; omega

theorem vreg_scratch (k : Fin 16) :
    vreg k ≠ .v24 ∧ vreg k ≠ .v25 ∧ vreg k ≠ .v26 ∧ vreg k ≠ .v27 :=
  (show ∀ k : Fin 16, vreg k ≠ .v24 ∧ vreg k ≠ .v25 ∧ vreg k ≠ .v26 ∧ vreg k ≠ .v27
    by decide) k

def transposed (s : State) (r j : Fin 4) : BitVec 128 :=
  ofVWords (vword (s.v (vreg (rowWord r 0))) j) (vword (s.v (vreg (rowWord r 1))) j)
    (vword (s.v (vreg (rowWord r 2))) j) (vword (s.v (vreg (rowWord r 3))) j)

structure TPrep (s₀ : State) (r : Fin 4) (s : State) : Prop where
  t24 : s.v .v24 = VPermOp.eval .zip1 .s4 (s₀.v (vreg (rowWord r 0))) (s₀.v (vreg (rowWord r 1)))
  t25 : s.v .v25 = VPermOp.eval .zip2 .s4 (s₀.v (vreg (rowWord r 0))) (s₀.v (vreg (rowWord r 1)))
  t26 : s.v .v26 = VPermOp.eval .zip1 .s4 (s₀.v (vreg (rowWord r 2))) (s₀.v (vreg (rowWord r 3)))
  t27 : s.v .v27 = VPermOp.eval .zip2 .s4 (s₀.v (vreg (rowWord r 2))) (s₀.v (vreg (rowWord r 3)))
  keep : ∀ k : Fin 16, s.v (vreg k) = s₀.v (vreg k)
  same : Same s₀ s

theorem transposePrep_ok (s : State) (r : Fin 4) :
    WP isa (.block (transposePrep (vreg (rowWord r 0)) (vreg (rowWord r 1))
      (vreg (rowWord r 2)) (vreg (rowWord r 3)))) s (TPrep s r) := by
  have hn0 := fun k => (vreg_scratch k).1
  have hn1 := fun k => (vreg_scratch k).2.1
  have hn2 := fun k => (vreg_scratch k).2.2.1
  have hn3 := fun k => (vreg_scratch k).2.2.2
  apply WP.of_runBlock
  simp (config := {decide := true}) only [transposePrep, runBlock_cons, runBlock_nil,
    exec, VOp.eval, isa, runStep_some, Option.map_some, Option.some.injEq,
    exists_eq_left', RegUpd.v_setV, hn0, hn1, hn2, ite_false]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.v_setV]; rfl
  · simp only [RegUpd.v_setV]; rfl
  · simp only [RegUpd.v_setV]; rfl
  · exact RegUpd.v_setV_self _ _ _
  · intro k; simp only [RegUpd.v_setV, hn0, hn1, hn2, hn3, ite_false]

theorem transposeEnd_ok {s₀ s : State} {r : Fin 4} (h : TPrep s₀ r s) :
    WP isa (.block (transposeEnd (vreg (rowWord r 0)) (vreg (rowWord r 1))
      (vreg (rowWord r 2)) (vreg (rowWord r 3)))) s fun s' =>
      (∀ j : Fin 4, s'.v (vreg (rowWord r j)) = transposed s₀ r j) ∧
      (∀ k : Fin 16, k.val / 4 ≠ r.val → s'.v (vreg k) = s₀.v (vreg k)) ∧ Same s₀ s' := by
  have hn0 := fun k => Ne.symm (vreg_scratch k).1
  have hn1 := fun k => Ne.symm (vreg_scratch k).2.1
  have hn2 := fun k => Ne.symm (vreg_scratch k).2.2.1
  have hn3 := fun k => Ne.symm (vreg_scratch k).2.2.2
  apply WP.of_runBlock
  simp only [transposeEnd, runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.v_setV,
    hn0, hn1, hn2, hn3, ite_false, h.t24, h.t25, h.t26, h.t27]
  refine ⟨?_, ?_, h.same.gpr, h.same.mem, h.same.rd, h.same.wr, h.same.sp⟩
  · intro j
    rcases j with ⟨j, hj⟩
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [vreg_inj, rowWord_inj] <;>
      simp (config := {decide := true}) only [Fin.ext_iff,
        ite_true, ite_false, zip1_s4, zip2_s4, zip1_d2, zip2_d2,
        vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3, transposed]
  · intro k hk
    have hne (j : Fin 4) : k ≠ rowWord r j := by
      intro e; subst k; simp only [rowWord] at hk; omega
    simp only [vreg_inj, hne, ite_false, h.keep]

theorem transpose_ok (s : State) (r : Fin 4) :
    WP isa (.block (transpose (vreg (rowWord r 0)) (vreg (rowWord r 1))
      (vreg (rowWord r 2)) (vreg (rowWord r 3)))) s fun s' =>
      (∀ j : Fin 4, s'.v (vreg (rowWord r j)) = transposed s r j) ∧
      (∀ k : Fin 16, k.val / 4 ≠ r.val → s'.v (vreg k) = s.v (vreg k)) ∧ Same s s' :=
  WP.block_append ((transposePrep_ok s r).mono fun _ h => transposeEnd_ok h)

end VG.Proof.ChaCha20.AArch64.Neon4

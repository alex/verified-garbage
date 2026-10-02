import VerifiedGarbage.Proof.X448.Wide.Pack

/-! Untrusted: wide coefficient addition for reduction modulo the X448 prime. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (read_x)

theorem addRegs_ok (s : State)
    (h : pair (s.gpr .x4) (s.gpr .x5) + pair (s.gpr .x6) (s.gpr .x9) < 2 ^ 128) :
    WP isa (.block [.adds .x .x4 .x4 .x6, .adcs .x .x5 .x5 .x9]) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) =
        pair (s.gpr .x4) (s.gpr .x5) + pair (s.gpr .x6) (s.gpr .x9) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · have hv := addPair128 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x9) h
    dsimp only [addCarry, carryOut, Size.bits] at hv ⊢
    exact hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_addWithCarry, hr, ite_false]

theorem addCoeff_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 16)
    (h : pair (s.gpr .x4) (s.gpr .x5) + coeff s.mem base ACC i < 2 ^ 128) :
    WP isa (.block (addCoeff i)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = pair (s.gpr .x4) (s.gpr .x5) + coeff s.mem base ACC i ∧
      t.mem = s.mem ∧ Keeps colRegs s t := by
  rw [show addCoeff i = [ld .x6 (ACC + 16 * i), ld .x9 (ACC + 16 * i + 8)] ++
    [.adds .x .x4 .x4 .x6, .adcs .x .x5 .x5 .x9] from rfl, WP.block_append_iff]
  have load := loadTerm_ok hs (a := ACC + 16 * i) (b := ACC + 16 * i + 8)
    (i := 0) (j := 0) (by simp only [ACC]; omega) (by simp only [ACC]; omega)
    (by simp only [ACC]; omega) (by simp only [ACC]; omega) (by decide) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at load
  refine WP.mono load fun u ⟨u6, u9, um, uk⟩ => ?_
  have uv : pair (u.gpr .x4) (u.gpr .x5) = pair (s.gpr .x4) (s.gpr .x5) := by
    rw [uk.1 .x4 (by decide), uk.1 .x5 (by decide)]
  have up : pair (u.gpr .x6) (u.gpr .x9) = coeff s.mem base ACC i := by rw [u6, u9]
  refine WP.mono (addRegs_ok u (by rw [uv, up]; exact h)) fun t ⟨tv, tm, tk⟩ => ?_
  exact ⟨by rw [tv, uv, up], tm.trans um, (uk.mono (by decide)).trans (tk.mono (by decide))⟩

theorem addCoeffs_ok {s : State} {base : Addr} (hs : Scr s base) (xs : List Nat)
    (hx : ∀ i ∈ xs, i < 16)
    (h : pair (s.gpr .x4) (s.gpr .x5) + (xs.map (coeff s.mem base ACC)).sum < 2 ^ 128) :
    WP isa (.block (xs.flatMap addCoeff)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) =
        pair (s.gpr .x4) (s.gpr .x5) + (xs.map (coeff s.mem base ACC)).sum ∧
      t.mem = s.mem ∧ Keeps colRegs s t := by
  induction xs generalizing s with
  | nil =>
    simp only [List.flatMap_nil, List.map_nil, List.sum_nil, Nat.add_zero]
    exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | cons i xs ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have hi := hx i List.mem_cons_self
    have hc : pair (s.gpr .x4) (s.gpr .x5) + coeff s.mem base ACC i < 2 ^ 128 := by
      simp only [List.map_cons, List.sum_cons] at h
      omega
    refine WP.mono (addCoeff_ok hs hi hc) fun u ⟨uv, um, uk⟩ => ?_
    refine WP.mono (ih (hs.of_keeps uk (by decide))
      (fun j hj => hx j (List.mem_cons_of_mem _ hj)) (by
        rw [uv, um]
        simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using h)) fun t ⟨tv, tm, tk⟩ => ?_
    refine ⟨?_, tm.trans um, uk.trans tk⟩
    rw [tv, uv, um]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

end VG.Proof.X448.Wide

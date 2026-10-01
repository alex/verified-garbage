import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Steps

namespace VG.Proof.Poly1305.AArch64.Radix64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.Limbs64 VG.PowLit
open VG.Spec.Poly1305 (P)

theorem select_zero (x y : BitVec 64) : x ^^^ ((y ^^^ x) &&& ((0 : BitVec 64) - 0)) = x := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]

theorem select_one (x y : BitVec 64) : x ^^^ ((y ^^^ x) &&& ((0 : BitVec 64) - 1)) = y := by
  rw [show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, BitVec.xor_comm y,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem fiveimm : (5#16).setWidth 64 = 5#64 := by decide

theorem reduce_eq : reduce = plus5 ++ (mask ++
    (selectLimb .x4 .x9 ++ selectLimb .x5 .x10 ++ selectLimb .x6 .x11)) := by
  simp only [reduce, List.append_assoc]

set_option simprocs false in
theorem plus5_ok (s : State) :
    WP isa (.block plus5) s fun s' =>
      (hval s + 5 < 2 ^ 192 →
        (s'.gpr .x9).toNat + 2 ^ 64 * (s'.gpr .x10).toNat + 2 ^ 128 * (s'.gpr .x11).toNat =
          hval s + 5) ∧ Keeps [.x9, .x10, .x11, .x13, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [plus5, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, gpr_addWithCarry, c_addWithCarry,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_zero, fiveimm,
    Option.some.injEq, exists_eq_left', ofNat_bool]
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := add3_toNat (s.gpr .x4) 5 (s.gpr .x5) 0 (s.gpr .x6) 0
      (by change (s.gpr .x4).toNat + 5 + 2 ^ 64 * ((s.gpr .x5).toNat + 0) +
          2 ^ 128 * ((s.gpr .x6).toNat + 0) < _
          simp only [hval] at h; omega_using [h])
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, zero_nat, Nat.add_zero] at e
    change _ = (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat + 5
    simp only [zero_nat, Nat.add_zero]
    have h5 : (5#64).toNat = 5 := rfl
    simp only [h5] at e ⊢
    omega_using [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

set_option simprocs false in
theorem mask_ok (s : State) :
    WP isa (.block mask) s fun s' =>
      s'.gpr .x12 = (0 : BitVec 64) - (s.gpr .x11 >>> 2) ∧
      s'.gpr .x11 = s.gpr .x11 &&& 3 ∧ Keeps [.x11, .x12, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mask, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, ite_true, ite_false,
    Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, BitVec.setWidth_zero, threeimm,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

set_option simprocs false in
theorem select_ok (s : State) :
    WP isa (.block (selectLimb .x4 .x9 ++ selectLimb .x5 .x10 ++ selectLimb .x6 .x11)) s fun s' =>
      s'.gpr .x4 = s.gpr .x4 ^^^ ((s.gpr .x9 ^^^ s.gpr .x4) &&& s.gpr .x12) ∧
      s'.gpr .x5 = s.gpr .x5 ^^^ ((s.gpr .x10 ^^^ s.gpr .x5) &&& s.gpr .x12) ∧
      s'.gpr .x6 = s.gpr .x6 ^^^ ((s.gpr .x11 ^^^ s.gpr .x6) &&& s.gpr .x12) ∧
      Keeps [.x4, .x5, .x6, .x13] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [selectLimb, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    gpr_write, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' =>
      ((s.gpr .x6).toNat ≤ 4 → hval s' = hval s % P) ∧
      Keeps [.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14] s s' := by
  have g0 := (s.gpr .x4).isLt; have g1 := (s.gpr .x5).isLt
  rw [reduce_eq]
  refine WP.block_append (WP.mono (plus5_ok s) fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (mask_ok s₁) fun s₂ ⟨m₁, m₂, k₂⟩ => ?_)
  refine WP.mono (select_ok s₂) fun s₃ ⟨c₁, c₂, c₃, k₃⟩ => ?_
  refine ⟨fun hh2 => ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have e₁ := e₁ (by simp only [hval]; omega_using [g0, g1, hh2])
  have ga := (s₁.gpr .x9).isLt; have gd := (s₁.gpr .x10).isLt
  have hg2 : (s₁.gpr .x11).toNat ≤ 5 := by simp only [hval] at e₁; omega_using [g0, g1, hh2, e₁]
  have r11₂ : s₂.gpr .x4 = s.gpr .x4 := (k₁.trans k₂).gpr'
  have rbx₂ : s₂.gpr .x5 = s.gpr .x5 := (k₁.trans k₂).gpr'
  have rbp₂ : s₂.gpr .x6 = s.gpr .x6 := (k₁.trans k₂).gpr'
  have rax₂ : s₂.gpr .x9 = s₁.gpr .x9 := k₂.gpr'
  have rdx₂ : s₂.gpr .x10 = s₁.gpr .x10 := k₂.gpr'
  rw [r11₂, rax₂, m₁] at c₁; rw [rbx₂, rdx₂, m₁] at c₂; rw [rbp₂, m₂, m₁] at c₃
  have ht : (s₁.gpr .x11 >>> 2).toNat = (s₁.gpr .x11).toNat / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [hval, c₁, c₂, c₃]
  unfold hval at e₁
  have hP : P = 2 ^ 130 - 5 := rfl
  by_cases hge : 4 ≤ (s₁.gpr .x11).toNat
  · have h1 : s₁.gpr .x11 >>> 2 = 1 := BitVec.eq_of_toNat_eq (by rw [ht]; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.one_mod]; omega_using [hg2, ht, hge])
    rw [h1, select_one, select_one, select_one, and3_toNat]
    have ge : P ≤ (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat := by
      omega_using [e₁, hg2, hP, hge]
    have lt : (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat - P <
        P := by omega_using [g0, g1, hh2, e₁, hP, ge]
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt lt]
    omega_using [g0, g1, hh2, e₁, hP, ge, lt]
  · have h0 : s₁.gpr .x11 >>> 2 = 0 := BitVec.eq_of_toNat_eq (by rw [ht]; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.div_eq_zero_iff, reduceCtorEq, false_or]; omega_using [hg2, hge])
    have lt : (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat <
        P := by omega_using [e₁, hg2, hP, hge]
    rw [h0, select_zero, select_zero, select_zero, Nat.mod_eq_of_lt lt]


end VG.Proof.Poly1305.AArch64.Radix64

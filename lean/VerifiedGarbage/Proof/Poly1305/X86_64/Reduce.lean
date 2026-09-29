import VerifiedGarbage.Proof.Poly1305.X86_64.Absorb

/-!
# Poly1305 on x86-64: the final reduction

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P)

theorem se5 : BitVec.signExtend 64 (5 : BitVec 32) = 5 := by decide

theorem select_zero (x y : BitVec 64) : x ^^^ ((y ^^^ x) &&& ((0 : BitVec 64) - 0)) = x := by simp
theorem select_one (x y : BitVec 64) : x ^^^ ((y ^^^ x) &&& ((0 : BitVec 64) - 1)) = y := by
  rw [show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, BitVec.xor_comm y,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem reduce_eq : reduce =
    ([.mov .rax (.reg .r11), .alu .add .rax (.imm 5), .mov .rdx (.reg .rbx), .alu .adc .rdx (.imm 0),
      .mov .r12 (.reg .rbp), .alu .adc .r12 (.imm 0)] : List Instr) ++
    (([.mov .r13 (.reg .r12), .shift .shr .r13 2, .mov32 .r14 (.imm 0), .alu .sub .r14 (.reg .r13),
      .alu .and .r12 (.imm 3)] : List Instr) ++
    ([.alu .xor .rax (.reg .r11), .alu .and .rax (.reg .r14), .alu .xor .r11 (.reg .rax),
      .alu .xor .rdx (.reg .rbx), .alu .and .rdx (.reg .r14), .alu .xor .rbx (.reg .rdx),
      .alu .xor .r12 (.reg .rbp), .alu .and .r12 (.reg .r14), .alu .xor .rbp (.reg .r12)] : List Instr)) := rfl

set_option simprocs false in
/-- `g = h + 5` into `rax, rdx, r12`. -/
theorem plus5_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .r11), .alu .add .rax (.imm 5), .mov .rdx (.reg .rbx),
      .alu .adc .rdx (.imm 0), .mov .r12 (.reg .rbp), .alu .adc .r12 (.imm 0)]) s fun s' =>
      (hval s + 5 < 2 ^ 192 →
        (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat + 2 ^ 128 * (s'.gpr .r12).toNat =
          hval s + 5) ∧ Keeps [.rax, .rdx, .r12] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, se0, se5]
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have hz : (0 : BitVec 64).toNat = 0 := rfl
    have h5 : (5 : BitVec 64).toNat = 5 := rfl
    rw [add3_toNat _ _ _ _ _ _ (by rw [hz, h5]; simp only [hval] at h; omega), hz, h5]
    simp only [hval]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2]

set_option simprocs false in
/-- The mask `-(g2 / 4)` into `r14`, and `g2 mod 4` into `r12`. -/
theorem mask_ok (s : State) :
    WP isa (.block [.mov .r13 (.reg .r12), .shift .shr .r13 2, .mov32 .r14 (.imm 0),
      .alu .sub .r14 (.reg .r13), .alu .and .r12 (.imm 3)]) s fun s' =>
      s'.gpr .r14 = (0 : BitVec 64) - (s.gpr .r12 >>> 2) ∧ s'.gpr .r12 = s.gpr .r12 &&& 3 ∧
      Keeps [.r12, .r13, .r14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, readSrc32, execAlu, execShift, arithFlags, State.setReg, State.setReg32, State.setFlags,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, se3]
  refine ⟨by simp, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2.1, hr.2.2]

set_option simprocs false in
/-- Selecting `rax, rdx, r12` over `r11, rbx, rbp` where the mask `r14` is set. -/
theorem select_ok (s : State) :
    WP isa (.block [.alu .xor .rax (.reg .r11), .alu .and .rax (.reg .r14), .alu .xor .r11 (.reg .rax),
      .alu .xor .rdx (.reg .rbx), .alu .and .rdx (.reg .r14), .alu .xor .rbx (.reg .rdx),
      .alu .xor .r12 (.reg .rbp), .alu .and .r12 (.reg .r14), .alu .xor .rbp (.reg .r12)]) s fun s' =>
      s'.gpr .r11 = s.gpr .r11 ^^^ ((s.gpr .rax ^^^ s.gpr .r11) &&& s.gpr .r14) ∧
      s'.gpr .rbx = s.gpr .rbx ^^^ ((s.gpr .rdx ^^^ s.gpr .rbx) &&& s.gpr .r14) ∧
      s'.gpr .rbp = s.gpr .rbp ^^^ ((s.gpr .r12 ^^^ s.gpr .rbp) &&& s.gpr .r14) ∧
      Keeps [.rax, .rdx, .r12, .r11, .rbx, .rbp] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false]
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' =>
      ((s.gpr .rbp).toNat ≤ 4 → hval s' = hval s % P) ∧
      Keeps [.rax, .rdx, .r11, .rbx, .rbp, .r12, .r13, .r14] s s' := by
  have g0 := (s.gpr .r11).isLt; have g1 := (s.gpr .rbx).isLt
  rw [reduce_eq]
  refine WP.block_append (WP.mono (plus5_ok s) fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (mask_ok s₁) fun s₂ ⟨m₁, m₂, k₂⟩ => ?_)
  refine WP.mono (select_ok s₂) fun s₃ ⟨c₁, c₂, c₃, k₃⟩ => ?_
  refine ⟨fun hh2 => ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have e₁ := e₁ (by simp only [hval]; omega)
  have ga := (s₁.gpr .rax).isLt; have gd := (s₁.gpr .rdx).isLt
  have hg2 : (s₁.gpr .r12).toNat ≤ 5 := by simp only [hval] at e₁; omega
  have r11₂ : s₂.gpr .r11 = s.gpr .r11 := (k₁.trans k₂).gpr'
  have rbx₂ : s₂.gpr .rbx = s.gpr .rbx := (k₁.trans k₂).gpr'
  have rbp₂ : s₂.gpr .rbp = s.gpr .rbp := (k₁.trans k₂).gpr'
  have rax₂ : s₂.gpr .rax = s₁.gpr .rax := k₂.gpr'
  have rdx₂ : s₂.gpr .rdx = s₁.gpr .rdx := k₂.gpr'
  rw [r11₂, rax₂, m₁] at c₁; rw [rbx₂, rdx₂, m₁] at c₂; rw [rbp₂, m₂, m₁] at c₃
  have ht : (s₁.gpr .r12 >>> 2).toNat = (s₁.gpr .r12).toNat / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [hval, c₁, c₂, c₃]
  unfold hval at e₁
  have hP : P = 2 ^ 130 - 5 := rfl
  by_cases hge : 4 ≤ (s₁.gpr .r12).toNat
  · have h1 : s₁.gpr .r12 >>> 2 = 1 := BitVec.eq_of_toNat_eq (by rw [ht]; simp; omega)
    rw [h1, select_one, select_one, select_one, and3_toNat]
    have ge : P ≤ (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat := by
      omega
    have lt : (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat - P <
        P := by omega
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt lt]
    omega
  · have h0 : s₁.gpr .r12 >>> 2 = 0 := BitVec.eq_of_toNat_eq (by rw [ht]; simp; omega)
    have lt : (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat <
        P := by omega
    rw [h0, select_zero, select_zero, select_zero, Nat.mod_eq_of_lt lt]

end VG.Proof.Poly1305.X86_64

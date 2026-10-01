import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Proof.Argon2.Divide

/-! # Complete fixed-time division for Argon2's indices -/

namespace VG.Proof.Argon2.X86_64.Divide

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Divide

theorem prefix_step (x : BitVec 64) (j : Nat) :
    x.toNat / 2 ^ j = 2 * (x.toNat / 2 ^ (j + 1)) + (x.getLsbD j).toNat := by
  have h := Nat.mod_add_div (x.toNat / 2 ^ j) 2
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ] at h
  simp only [Nat.succ_eq_add_one] at h
  simp only [← BitVec.testBit_toNat, Nat.toNat_testBit]
  omega

def changed : List Reg := [.rcx, .r8, .r10, .rax, .r9]

/-- The already-consumed prefix equals quotient times divisor plus remainder. -/
structure Invariant (n : Nat) (s : State) : Prop where
  numerator : (s.gpr .rdi).toNat < 2 ^ 32
  divisor : 0 < (s.gpr .rsi).toNat
  divisorBound : (s.gpr .rsi).toNat < 2 ^ 32
  remainder : (s.gpr .r8).toNat < (s.gpr .rsi).toNat
  equation : (s.gpr .rdi).toNat / 2 ^ n =
    (s.gpr .r9).toNat * (s.gpr .rsi).toNat + (s.gpr .r8).toNat

theorem bit_invariant (s : State) (n : Nat) (hn : n < 32) (h : Invariant (n + 1) s) :
    WP isa (.block (bit n)) s fun t => Invariant n t ∧ Keeps changed s t := by
  have hqmul := Nat.le_mul_of_pos_right (s.gpr .r9).toNat h.divisor
  have hprefix := Nat.div_le_self (s.gpr .rdi).toNat (2 ^ (n + 1))
  have he := h.equation
  have hb := h.numerator
  have hq : (s.gpr .r9).toNat < 2 ^ 32 := by omega
  have hr : (s.gpr .r8).toNat < 2 ^ 32 := Nat.lt_trans h.remainder h.divisorBound
  refine (bit_ok s n hn hr hq).mono ?_
  rintro t ⟨ht8, ht9, ht⟩
  have hdi := ht.regs .rdi (by decide)
  have hsi := ht.regs .rsi (by decide)
  have hs := VG.Proof.Argon2.divide_step h.equation h.remainder
    (Bool.toNat_le ((s.gpr .rdi).getLsbD n))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ht⟩
  · rw [hdi]; exact h.numerator
  · rw [hsi]; exact h.divisor
  · rw [hsi]; exact h.divisorBound
  · rw [ht8, hsi]; exact hs.2
  · rw [hdi, hsi, ht8, ht9, prefix_step]
    exact hs.1

theorem bits_ok (n : Nat) (hn : n ≤ 32) (s : State) (h : Invariant n s) :
    WP isa (.block ((List.range n).reverse.flatMap bit)) s fun t =>
      Invariant 0 t ∧ Keeps changed s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨h, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine (bit_invariant s n (by omega) h).mono ?_
    rintro t ⟨ht, kt⟩
    refine (ih (by omega) t ht).mono ?_
    rintro u ⟨hu, ku⟩
    exact ⟨hu, kt.trans ku⟩

theorem setup_ok (s : State) (hn : (s.gpr .rdi).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .rsi).toNat) (hd' : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa (.block [.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 0),
      .mov32 .rax (.imm 0), .alu .cmp .rax (.imm 0)]) s fun t =>
      Invariant 32 t ∧ Keeps changed s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, readSrc, execAlu,
    RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨hn, hd, hd', ?_, ?_⟩, ?_⟩
  · exact hd
  · change (s.gpr .rdi).toNat / 2 ^ 32 = 0 * (s.gpr .rsi).toNat + 0
    rw [Nat.div_eq_of_lt hn, Nat.zero_mul, Nat.zero_add]
  · constructor
    · intro r hr
      simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
    all_goals rfl

theorem code_ok (s : State) (hn : (s.gpr .rdi).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .rsi).toNat) (hd' : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      (t.gpr .r9).toNat = (s.gpr .rdi).toNat / (s.gpr .rsi).toNat ∧
      (t.gpr .r8).toNat = (s.gpr .rdi).toNat % (s.gpr .rsi).toNat ∧
      Keeps changed s t := by
  rw [code, WP.block_append_iff]
  refine (setup_ok s hn hd hd').mono ?_
  rintro u ⟨hu, ku⟩
  refine (bits_ok 32 (by decide) u hu).mono ?_
  rintro t ⟨ht, kt⟩
  have k := ku.trans kt
  have he := ht.equation
  simp only [Nat.pow_zero, Nat.div_one] at he
  obtain ⟨hq, hr⟩ := VG.Proof.Argon2.divide_result ht.divisor he ht.remainder
  rw [k.regs .rdi (by decide), k.regs .rsi (by decide)] at hq hr
  exact ⟨hq, hr, k⟩

end VG.Proof.Argon2.X86_64.Divide

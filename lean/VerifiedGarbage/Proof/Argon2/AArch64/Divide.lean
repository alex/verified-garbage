import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.Divide

/-! # Complete fixed-time division for Argon2's indices -/

namespace VG.Proof.Argon2.AArch64.Divide

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Divide

theorem prefix_step (x : BitVec 64) (j : Nat) :
    x.toNat / 2 ^ j = 2 * (x.toNat / 2 ^ (j + 1)) + (x.getLsbD j).toNat := by
  have h := Nat.mod_add_div (x.toNat / 2 ^ j) 2
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ] at h
  simp only [Nat.succ_eq_add_one] at h
  simp only [← BitVec.testBit_toNat, Nat.toNat_testBit]
  omega

def changed : List Reg := [.x3, .x4, .x6, .x8, .x5, .x9]

/-- The already-consumed prefix equals quotient times divisor plus remainder. -/
structure Invariant (n : Nat) (s : State) : Prop where
  numerator : (s.gpr .x0).toNat < 2 ^ 32
  divisor : 0 < (s.gpr .x1).toNat
  divisorBound : (s.gpr .x1).toNat < 2 ^ 32
  remainder : (s.gpr .x4).toNat < (s.gpr .x1).toNat
  equation : (s.gpr .x0).toNat / 2 ^ n =
    (s.gpr .x5).toNat * (s.gpr .x1).toNat + (s.gpr .x4).toNat

theorem bit_invariant (s : State) (n : Nat) (hn : n < 32) (h : Invariant (n + 1) s) :
    WP isa (.block (bit n)) s fun t => Invariant n t ∧ Keeps changed s t := by
  have hqmul := Nat.le_mul_of_pos_right (s.gpr .x5).toNat h.divisor
  have hprefix := Nat.div_le_self (s.gpr .x0).toNat (2 ^ (n + 1))
  have he := h.equation
  have hb := h.numerator
  have hq : (s.gpr .x5).toNat < 2 ^ 32 := by omega
  have hr : (s.gpr .x4).toNat < 2 ^ 32 := Nat.lt_trans h.remainder h.divisorBound
  refine (bit_ok s n hn hr hq h.divisorBound).mono ?_
  rintro t ⟨ht8, ht9, ht⟩
  have hdi := ht.regs .x0 (by decide)
  have hsi := ht.regs .x1 (by decide)
  have hs := VG.Proof.Argon2.divide_step h.equation h.remainder
    (Bool.toNat_le ((s.gpr .x0).getLsbD n))
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

theorem setup_ok (s : State) (hn : (s.gpr .x0).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .x1).toNat) (hd' : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa (.block setup) s fun t =>
      Invariant 32 t ∧ Keeps changed s t := by
  apply WP.of_runBlock
  simp only [setup, runBlock_cons, runStep_some, runBlock_nil, exec,
    Size.bits,
    ite_true, Option.some.injEq, exists_eq_left',
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero]
  refine ⟨⟨hn, hd, hd', ?_, ?_⟩, ?_⟩
  · exact hd
  · change (s.gpr .x0).toNat / 2 ^ 32 = 0 * (s.gpr .x1).toNat + 0
    rw [Nat.div_eq_of_lt hn, Nat.zero_mul, Nat.zero_add]
  · constructor
    · intro r hr
      simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.2.1, hr.2.2.2.2.1, ite_false]
    all_goals rfl

theorem code_ok (s : State) (hn : (s.gpr .x0).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .x1).toNat) (hd' : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      (t.gpr .x5).toNat = (s.gpr .x0).toNat / (s.gpr .x1).toNat ∧
      (t.gpr .x4).toNat = (s.gpr .x0).toNat % (s.gpr .x1).toNat ∧
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
  rw [k.regs .x0 (by decide), k.regs .x1 (by decide)] at hq hr
  exact ⟨hq, hr, k⟩

end VG.Proof.Argon2.AArch64.Divide

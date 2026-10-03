import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Instruction-level proofs for the radix-64 Poly1305 arithmetic. -/
namespace VG.Proof.Poly1305.AArch64.Radix64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.Limbs64 VG.PowLit

def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.gpr' {rs : List Reg} {s s' : State} (h : Keeps rs s s') {r : Reg}
    (hr : r ∉ rs := by decide) : s'.gpr r = s.gpr r := h.1 r hr

theorem Keeps.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂)
    (h₂ : Keeps rs' s₂ s₃) : Keeps (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1],
   h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

/-- The carry bit embedded in a word is target-independent. -/
theorem ofNat_bool (c : Bool) : BitVec.ofNat 64 c.toNat = (BitVec.ofBool c).setWidth 64 := by
  cases c <;> rfl

theorem threeimm : (3#16).setWidth 64 = 3#64 := by decide

theorem zero_nat : (0#64).toNat = 0 := rfl

theorem mul_words (a b : BitVec 64) :
    (a * b).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := by
  simpa only [BitVec.toNat_mul, BitVec.toNat_ofNat] using toNat_mul_lo a b

set_option simprocs false in
theorem mulTo_ok {lo hi a b : Reg} (s : State) (ha : a ≠ lo) (hb : b ≠ lo)
    (hlh : lo ≠ hi) :
    WP isa (.block (mulTo lo hi a b)) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr a).toNat * (s.gpr b).toNat ∧
      Keeps [lo, hi] s s' := by
  apply WP.of_runBlock
  simp only [mulTo, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, gpr_write, ha, hb, hlh,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨mul_words _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_write, hr.1, hr.2, ite_false]

set_option simprocs false in
theorem mulAdd_ok {lo hi a b : Reg} (s : State) (ha : a ≠ .x13) (hb : b ≠ .x13)
    (hl0 : lo ≠ .x13) (hl1 : lo ≠ .x14) (hh0 : hi ≠ .x13) (hh1 : hi ≠ .x14)
    (hlh : hi ≠ lo) :
    WP isa (.block (mulAdd lo hi a b)) s fun s' =>
      ((s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr b).toNat < 2 ^ 128 →
        (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat =
          (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr b).toNat) ∧
      Keeps [lo, hi, .x13, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mulAdd, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, gpr_addWithCarry, c_addWithCarry,
    ha, hb, hl0, hl1, hh0, hh1, hlh, hlh.symm, hl1.symm,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', ofNat_bool]
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := mul_words (s.gpr a) (s.gpr b)
    rw [add_adc_toNat _ _ _ _ (by omega_using [hlt, e])]
    omega_using [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]


abbrev hval (s : State) : Nat :=
  (s.gpr .x4).toNat + 2 ^ 64 * (s.gpr .x5).toNat + 2 ^ 128 * (s.gpr .x6).toNat

abbrev word (m : Mem) (p : Addr) (d : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 d) 64).toNat

set_option simprocs false in
theorem mulAddSmall_ok (s : State) :
    WP isa (.block (mulAddSmall .x11 .x12 .x6 .x17)) s fun s' =>
      ((s.gpr .x6).toNat * (s.gpr .x17).toNat < 2 ^ 64 →
        (s.gpr .x11).toNat + 2 ^ 64 * (s.gpr .x12).toNat +
          (s.gpr .x6).toNat * (s.gpr .x17).toNat < 2 ^ 128 →
        (s'.gpr .x11).toNat + 2 ^ 64 * (s'.gpr .x12).toNat =
          (s.gpr .x11).toNat + 2 ^ 64 * (s.gpr .x12).toNat +
            (s.gpr .x6).toNat * (s.gpr .x17).toNat) ∧ Keeps [.x11, .x12, .x13, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mulAddSmall, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, gpr_addWithCarry, c_addWithCarry,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_zero,
    Option.some.injEq, exists_eq_left', ofNat_bool]
  refine ⟨fun hp hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e : (s.gpr .x6 * s.gpr .x17).toNat = (s.gpr .x6).toNat * (s.gpr .x17).toNat := by
      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hp]
    have h := add_adc_toNat (s.gpr .x11) (s.gpr .x6 * s.gpr .x17) (s.gpr .x12) 0
      (by simp only [e, BitVec.ofNat_eq_ofNat, zero_nat, Nat.add_zero]; omega_using [hlt])
    simp only [e, BitVec.ofNat_eq_ofNat, zero_nat, Nat.add_zero, BitVec.add_zero] at h
    rw [e]
    omega_using [h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

set_option simprocs false in
theorem mulSmall_ok (s : State) :
    WP isa (.block [.mul .x .x13 .x6 .x7]) s fun s' =>
      ((s.gpr .x6).toNat * (s.gpr .x7).toNat < 2 ^ 64 →
        (s'.gpr .x13).toNat = (s.gpr .x6).toNat * (s.gpr .x7).toNat) ∧ Keeps [.x13] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]
  · simp only [List.mem_singleton] at hr
    exact gpr_write_of_ne _ _ _ hr

set_option simprocs false in
theorem combine_ok (s : State) :
    WP isa (.block combine) s fun s' =>
      ((s.gpr .x11).toNat + (s.gpr .x10).toNat +
          2 ^ 64 * ((s.gpr .x12).toNat + (s.gpr .x13).toNat) < 2 ^ 128 →
        (s'.gpr .x11).toNat + 2 ^ 64 * (s'.gpr .x12).toNat =
          (s.gpr .x11).toNat + (s.gpr .x10).toNat +
            2 ^ 64 * ((s.gpr .x12).toNat + (s.gpr .x13).toNat)) ∧ Keeps [.x11, .x12] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [combine, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, gpr_addWithCarry, c_addWithCarry,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', ofNat_bool]
  refine ⟨add_adc_toNat _ _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2, ite_false]

set_option simprocs false in
theorem fold_ok (s : State) :
    WP isa (.block fold) s fun s' =>
      s'.gpr .x4 = s.gpr .x9 ∧ s'.gpr .x5 = s.gpr .x11 ∧
      (s'.gpr .x6).toNat = (s.gpr .x12).toNat % 4 ∧
      ((s.gpr .x12).toNat < 2 ^ 63 → (s'.gpr .x13).toNat = 5 * ((s.gpr .x12).toNat / 4)) ∧
      Keeps [.x4, .x5, .x6, .x12, .x13, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [fold, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, ite_true, ite_false,
    Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    BitVec.shiftLeft_zero, threeimm, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, and3_toNat _, fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h3 := and3_toNat (s.gpr .x12)
    simp only [BitVec.ofNat_eq_ofNat] at h3
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h3]
    omega_using [h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

set_option simprocs false in
theorem addLow_ok (s : State) :
    WP isa (.block addLow) s fun s' =>
      (hval s + (s.gpr .x13).toNat < 2 ^ 192 → hval s' = hval s + (s.gpr .x13).toNat) ∧
      Keeps [.x4, .x5, .x6, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addLow, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, hval, gpr_write, gpr_addWithCarry, c_addWithCarry,
    ite_true, ite_false, Bool.toNat_false, Nat.add_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_zero,
    Option.some.injEq, exists_eq_left', ofNat_bool]
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := add3_toNat (s.gpr .x4) (s.gpr .x13) (s.gpr .x5) 0 (s.gpr .x6) 0
      (by simp only [BitVec.ofNat_eq_ofNat, zero_nat, Nat.add_zero]; omega_using [h])
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, zero_nat, Nat.add_zero] at e
    simp only [zero_nat, Nat.add_zero]
    omega_using [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]


theorem pad_word (pad : Bool) :
    ((if pad then (1 : BitVec 16) else 0).setWidth 64) = BitVec.ofNat 64 pad.toNat := by
  cases pad <;> rfl

set_option simprocs false in
theorem addBlock_ok (s : State) (pad : Bool)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 8) 8) :
    WP isa (.block (addBlock pad)) s fun s' =>
      (hval s + (word s.mem (s.gpr .x1) 0 + 2 ^ 64 * word s.mem (s.gpr .x1) 8 +
          2 ^ 128 * pad.toNat) < 2 ^ 192 →
        hval s' = hval s + (word s.mem (s.gpr .x1) 0 +
          2 ^ 64 * word s.mem (s.gpr .x1) 8 + 2 ^ 128 * pad.toNat)) ∧
      Keeps [.x4, .x5, .x6, .x13, .x14, .x15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addBlock, runBlock_cons, runStep_some,
    exec_ldr_x (show 0 % 8 = 0 ∧ 0 < 32768 by decide) h0,
    exec_ldr_x (show 8 % 8 = 0 ∧ 8 < 32768 by decide),
    gpr_write, mem_write, rd_write, wr_write, h8, ite_false]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, hval, gpr_write,
    gpr_addWithCarry, c_addWithCarry, ite_true, ite_false, Bool.toNat_false,
    Nat.add_zero, BitVec.add_zero, Nat.mul_zero,
    BitVec.shiftLeft_zero, Option.some.injEq, exists_eq_left', pad_word, ofNat_bool]
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have hp : ((BitVec.ofBool pad).setWidth 64).toNat = pad.toNat := carry_toNat pad
    have e := add3_toNat (s.gpr .x4) (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 0) 64)
      (s.gpr .x5) (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 8) 64)
      (s.gpr .x6) ((BitVec.ofBool pad).setWidth 64)
      (by simp only [hp]; simp only [word] at hlt; omega_using [hlt])
    rw [hp] at e
    simp only [BitVec.add_zero] at e
    simp only [word, BitVec.add_zero]
    omega_using [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

end VG.Proof.Poly1305.AArch64.Radix64

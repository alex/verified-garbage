import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Poly
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Steps
import VerifiedGarbage.Proof.Poly1305.AArch64.Blocks

/-!
# Poly1305 in nine registers (AArch64): one block

`Impl/ChaCha20Poly1305/AArch64/Poly.lean`, a part at a time: each part's
result as numbers, and the registers it writes (`Keeps`).
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Poly

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.ChaCha20Poly1305.AArch64.Poly
open VG.Proof.Poly1305.Limbs64 VG.PowLit
open VG.Proof.Poly1305.AArch64.Radix64 (Keeps Keeps.gpr' Keeps.trans Keeps.mono ofNat_bool
  mul_words word)
open VG.Spec.Poly1305 (P)

/-- The accumulator, as a number. -/
abbrev hval (s : State) : Nat :=
  (s.gpr .x21).toNat + 2 ^ 64 * (s.gpr .x22).toNat + 2 ^ 128 * (s.gpr .x23).toNat

theorem one16 : ((1 : BitVec 16).setWidth 64 : BitVec 64) = 1 := rfl
theorem zero16 : ((0 : BitVec 16).setWidth 64 : BitVec 64) = 0#64 := rfl
theorem three16 : ((3 : BitVec 16).setWidth 64 : BitVec 64) = 3#64 := rfl

set_option simprocs false in
theorem addBlock_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 8) 8) :
    WP isa (.block addBlock) s fun s' =>
      (hval s + (word s.mem (s.gpr .x20) 0 + 2 ^ 64 * word s.mem (s.gpr .x20) 8 + 2 ^ 128) <
          2 ^ 192 →
        hval s' = hval s + (word s.mem (s.gpr .x20) 0 + 2 ^ 64 * word s.mem (s.gpr .x20) 8 +
          2 ^ 128)) ∧
      Keeps [.x21, .x22, .x23, .x25, .x27, .x28] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addBlock, runBlock_cons, runStep_some,
    exec_ldr_x (show 0 % 8 = 0 ∧ 0 < 32768 by decide) h0,
    exec_ldr_x (show 8 % 8 = 0 ∧ 8 < 32768 by decide),
    gpr_write, mem_write, rd_write, wr_write, h8, ite_false]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, hval, gpr_write,
    gpr_addWithCarry, c_addWithCarry, ite_true, ite_false, Bool.toNat_false,
    Nat.add_zero, BitVec.add_zero, Nat.mul_zero,
    BitVec.shiftLeft_zero, Option.some.injEq, exists_eq_left', one16, ofNat_bool]
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have one : (1 : BitVec 64).toNat = 1 := BitVec.toNat_one (by decide)
    have hw : word s.mem (s.gpr .x20) 0 = (s.mem.readW (s.gpr .x20) 64).toNat := by
      simp only [word, BitVec.add_zero]
    have hw8 : word s.mem (s.gpr .x20) 8 = (s.mem.readW (s.gpr .x20 + 8#64) 64).toNat := rfl
    simp only [hw, hw8] at hlt ⊢
    have e := add3_toNat (s.gpr .x21) (s.mem.readW (s.gpr .x20) 64)
      (s.gpr .x22) (s.mem.readW (s.gpr .x20 + 8#64) 64) (s.gpr .x23) 1
      (by omega_using [hlt, one])
    omega_using [e, one]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- The word `r₀` or `r₁` of the key, at `[x0 + d]`. -/
abbrev rword (s : State) (d : Nat) : BitVec 64 := s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 d) 64

set_option simprocs false in
theorem mulR0_ok (s : State)
    (hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 r0Off) 8) :
    WP isa (.block mulR0) s fun s' =>
      ((rword s r0Off).toNat < 2 ^ 60 → (s.gpr .x23).toNat ≤ 6 →
        (s'.gpr .x25).toNat + 2 ^ 64 * (s'.gpr .x27).toNat + 2 ^ 128 * (s'.gpr .x28).toNat =
          hval s * (rword s r0Off).toNat ∧ (s'.gpr .x28).toNat < 2 ^ 63) ∧
      Keeps [.x24, .x25, .x27, .x28, .x30] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mulR0, r0Off, runBlock_cons, runStep_some,
    exec_ldr_x (show 224 % 8 = 0 ∧ 224 < 32768 by decide) hi]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, c_write,
    gpr_addWithCarry, c_addWithCarry, ite_true, ite_false, Bool.toNat_false,
    Nat.add_zero, BitVec.add_zero, Option.some.injEq, exists_eq_left', ofNat_bool]
  refine ⟨fun hr0 hh2 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [rword] at hr0 ⊢
    generalize hR : s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 224) 64 = R at hr0 ⊢
    have e0 := mul_words (s.gpr .x21) R
    have e1 := mul_words (s.gpr .x22) R
    have b0 := mul_lt (s.gpr .x21).isLt hr0
    have b1 := mul_lt (s.gpr .x22).isLt hr0
    have b2 := mul_le_lt hh2 hr0
    have m2 : (s.gpr .x23 * R).toNat = (s.gpr .x23).toNat * R.toNat := by
      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega_using [b2])]
    generalize hA : BitVec.ofNat 64 ((s.gpr .x21).toNat * R.toNat / 2 ^ 64) = A at e0 ⊢
    generalize hB : BitVec.ofNat 64 ((s.gpr .x22).toNat * R.toNat / 2 ^ 64) = B at e1 ⊢
    have e := add_adc_toNat A (s.gpr .x22 * R) (s.gpr .x23 * R) B
      (by rw [m2]; omega_using [e0, e1, b0, b1, b2])
    have k := (s.gpr .x23 * R + B + (BitVec.ofBool (decide (2 ^ 64 ≤ A.toNat +
      (s.gpr .x22 * R).toNat))).setWidth 64).isLt
    have hb : (s.gpr .x23 * R + B + (BitVec.ofBool (decide (2 ^ 64 ≤ A.toNat +
        (s.gpr .x22 * R).toNat))).setWidth 64).toNat < 2 ^ 63 := by
      omega_using [e, e0, e1, b0, b1, b2, m2, (A + s.gpr .x22 * R).isLt]
    refine ⟨?_, hb⟩
    simp only [hval]
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
    omega_using [e, e0, e1, m2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2,
      ite_false]

/-- An addition of a carry, with its carry out. -/
theorem addc_bit (a : BitVec 64) (c : Bool) :
    (a + (BitVec.ofBool c).setWidth 64).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + c.toNat)).toNat =
      a.toNat + c.toNat := by
  rw [BitVec.toNat_add, carry_toNat]
  have ha := a.isLt; have hc := Bool.toNat_le c
  by_cases h : 2 ^ 64 ≤ a.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    omega_using [ha, hc, h]

set_option simprocs false in
theorem mulR1_ok (s : State)
    (hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 r1Off) 8) :
    WP isa (.block mulR1) s fun s' =>
      ((rword s r1Off).toNat < 2 ^ 60 → (s.gpr .x23).toNat ≤ 6 → (s.gpr .x28).toNat < 2 ^ 63 →
        (s'.gpr .x27).toNat + 2 ^ 64 * (s'.gpr .x28).toNat + 2 ^ 128 * (s'.gpr .x30).toNat =
          (s.gpr .x27).toNat + 2 ^ 64 * (s.gpr .x28).toNat + hval s * (rword s r1Off).toNat) ∧
      Keeps [.x21, .x22, .x23, .x24, .x27, .x28, .x30] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mulR1, r1Off, runBlock_cons, runStep_some,
    exec_ldr_x (show 232 % 8 = 0 ∧ 232 < 32768 by decide) hi]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, c_write,
    gpr_addWithCarry, c_addWithCarry, ite_true, ite_false, Bool.toNat_false,
    Nat.add_zero, BitVec.add_zero, Option.some.injEq, exists_eq_left', ofNat_bool, zero16,
    Nat.mul_zero, BitVec.shiftLeft_zero]
  refine ⟨fun hr1 hh2 ht2 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [rword] at hr1 ⊢
    generalize hR : s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 232) 64 = R at hr1 ⊢
    have e0 := mul_words (s.gpr .x21) R
    have e1 := mul_words (s.gpr .x22) R
    have b0 := mul_lt (s.gpr .x21).isLt hr1
    have b1 := mul_lt (s.gpr .x22).isLt hr1
    have b2 := mul_le_lt hh2 hr1
    have m2 : (s.gpr .x23 * R).toNat = (s.gpr .x23).toNat * R.toNat := by
      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega_using [b2])]
    generalize hA : BitVec.ofNat 64 ((s.gpr .x21).toNat * R.toNat / 2 ^ 64) = A at e0 ⊢
    generalize hB : BitVec.ofNat 64 ((s.gpr .x22).toNat * R.toNat / 2 ^ 64) = B at e1 ⊢
    generalize hc1 : decide (2 ^ 64 ≤ (s.gpr .x27).toNat + (s.gpr .x21 * R).toNat) = c1
    have f1 := addc0 (s.gpr .x27) (s.gpr .x21 * R)
    rw [hc1] at f1
    generalize hc2 : decide (2 ^ 64 ≤ (s.gpr .x22 * R).toNat + A.toNat + c1.toNat) = c2
    have f2 := addc1 (s.gpr .x22 * R) A c1
    rw [hc2] at f2
    have f3 := addc1 (s.gpr .x23 * R) B c2
    generalize hX : s.gpr .x22 * R + A + (BitVec.ofBool c1).setWidth 64 = X at f2 ⊢
    generalize hY : s.gpr .x23 * R + B + (BitVec.ofBool c2).setWidth 64 = Y at f3 ⊢
    have f4 := addc0 (s.gpr .x28) X
    generalize hc3 : decide (2 ^ 64 ≤ (s.gpr .x28).toNat + X.toNat) = c3 at f4 ⊢
    have f5 := addc_bit Y c3
    have k1 := Bool.toNat_le c1; have k2 := Bool.toNat_le c2; have k3 := Bool.toNat_le c3
    have k4 := Bool.toNat_le (decide (2 ^ 64 ≤ (s.gpr .x23 * R).toNat + B.toNat + c2.toNat))
    have k5 := Bool.toNat_le (decide (2 ^ 64 ≤ Y.toNat + c3.toNat))
    have xa := (s.gpr .x21 * R).isLt; have xb := (s.gpr .x22 * R).isLt
    have xA := A.isLt; have xB := B.isLt; have xX := X.isLt; have xY := Y.isLt
    simp only [hval]
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
    omega_using [e0, e1, b0, b1, b2, m2, f1, f2, f3, f4, f5, k1, k2, k3, k4, k5, ht2, xa, xb,
      xA, xB, xX, xY]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

theorem extr2_toNat (hi lo : BitVec 64) :
    ((hi ++ lo).extractLsb' 2 64).toNat = lo.toNat / 4 + 2 ^ 62 * (hi.toNat % 4) := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := lo.isLt; have := hi.isLt
  omega

theorem and3' (x : BitVec 64) : (x &&& 3#64).toNat = x.toNat % 4 := and3_toNat x

/-- The arithmetic of `reduce`, on its four input words. -/
theorem reduce_arith (t0 t1 t2 t3 : BitVec 64) (ht3 : t3.toNat < 2 ^ 63) :
    (t2 - (t2 &&& 3#64) + t0 + BitVec.extractLsb' 2 64 (t3 ++ t2)).toNat +
        2 ^ 64 *
          (t3 + t3 >>> 2 +
                  BitVec.setWidth 64
                    (BitVec.ofBool (decide (2 ^ 64 ≤ (t2 - (t2 &&& 3#64)).toNat + t0.toNat))) +
                t1 +
              BitVec.setWidth 64
                (BitVec.ofBool
                  (decide
                    (2 ^ 64 ≤ (t2 - (t2 &&& 3#64) + t0).toNat +
                        (BitVec.extractLsb' 2 64 (t3 ++ t2)).toNat)))).toNat +
      2 ^ 128 *
        ((t2 &&& 3#64) +
            BitVec.setWidth 64
              (BitVec.ofBool
                (decide
                  (2 ^ 64 ≤
                    (t3 + t3 >>> 2 +
                            BitVec.setWidth 64
                              (BitVec.ofBool
                                (decide (2 ^ 64 ≤ (t2 - (t2 &&& 3#64)).toNat + t0.toNat)))).toNat +
                        t1.toNat +
                      (decide
                          (2 ^ 64 ≤ (t2 - (t2 &&& 3#64) + t0).toNat +
                              (BitVec.extractLsb' 2 64 (t3 ++ t2)).toNat)).toNat)))).toNat =
    t0.toNat + 2 ^ 64 * t1.toNat + 2 ^ 128 * (t2.toNat % 4) + 5 * (t2.toNat / 4 + 2 ^ 62 * t3.toNat) := by
  have a2 := and3' t2
  have a0 : (t2 - (t2 &&& 3#64)).toNat = t2.toNat - t2.toNat % 4 := by
    rw [BitVec.toNat_sub, a2]; have := t2.isLt; omega
  have ex := extr2_toNat t3 t2
  have sh : (t3 >>> 2).toNat = t3.toNat / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  generalize t2 &&& 3#64 = A2 at a2 a0 ⊢
  generalize t2 - A2 = A0 at a0 ⊢
  generalize (t3 ++ t2).extractLsb' 2 64 = E at ex ⊢
  generalize t3 >>> 2 = U at sh ⊢
  have f1 := addc0 A0 t0
  generalize decide (2 ^ 64 ≤ A0.toNat + t0.toNat) = c1 at f1 ⊢
  have f2 := addc1 t3 U c1
  generalize decide (2 ^ 64 ≤ t3.toNat + U.toNat + c1.toNat) = c2 at f2 ⊢
  generalize A0 + t0 = X at f1 ⊢
  generalize t3 + U + (BitVec.ofBool c1).setWidth 64 = Y at f2 ⊢
  have f3 := addc0 X E
  generalize decide (2 ^ 64 ≤ X.toNat + E.toNat) = c3 at f3 ⊢
  have f4 := addc1 Y t1 c3
  generalize decide (2 ^ 64 ≤ Y.toNat + t1.toNat + c3.toNat) = c4 at f4 ⊢
  have f5 := addc_bit A2 c4
  have k1 := Bool.toNat_le c1; have k2 := Bool.toNat_le c2; have k3 := Bool.toNat_le c3
  have k4 := Bool.toNat_le c4
  have k5 := Bool.toNat_le (decide (2 ^ 64 ≤ A2.toNat + c4.toNat))
  have xt0 := t0.isLt; have xt1 := t1.isLt; have xt2 := t2.isLt; have xt3 := t3.isLt
  have xY := Y.isLt; have xX := X.isLt; have xE := E.isLt; have xA0 := A0.isLt
  have z2 : c2.toNat = 0 := by omega_using [f2, sh, ht3, k1, k2, xY]
  have hE : E.toNat + 2 ^ 64 * (t3.toNat / 4) = t2.toNat / 4 + 2 ^ 62 * t3.toNat := by
    omega_using [ex]
  have hY : Y.toNat = t3.toNat + t3.toNat / 4 + c1.toNat := by omega_using [f2, z2, sh]
  have z5 : (decide (2 ^ 64 ≤ A2.toNat + c4.toNat)).toNat = 0 := by
    omega_using [f5, a2, k4, k5]
  have hs : (X + E).toNat + 2 ^ 64 * (Y + t1 + (BitVec.ofBool c3).setWidth 64).toNat +
      2 ^ 128 * (A2 + (BitVec.ofBool c4).setWidth 64).toNat =
      X.toNat + E.toNat + 2 ^ 64 * (Y.toNat + t1.toNat) + 2 ^ 128 * A2.toNat := by
    omega_using [f3, f4, f5, z5]
  rw [hs, hY]
  omega_using [a2, a0, hE, f1]

set_option simprocs false in
theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' =>
      ((s.gpr .x30).toNat < 2 ^ 63 →
        hval s' = (s.gpr .x25).toNat + 2 ^ 64 * (s.gpr .x27).toNat +
          2 ^ 128 * ((s.gpr .x28).toNat % 4) +
          5 * ((s.gpr .x28).toNat / 4 + 2 ^ 62 * (s.gpr .x30).toNat)) ∧
      s'.gpr .x20 = s.gpr .x20 + 16#64 ∧
      Keeps [.x20, .x21, .x22, .x23, .x25, .x28] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [reduce, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, BitVec.setWidth_eq, gpr_write, c_write,
    gpr_addWithCarry, c_addWithCarry, ite_true, ite_false, Bool.toNat_false,
    Nat.add_zero, BitVec.add_zero, Option.some.injEq, exists_eq_left', ofNat_bool, zero16,
    three16, Nat.mul_zero, BitVec.shiftLeft_zero, hval]
  refine ⟨fun ht3 => reduce_arith _ _ _ _ ht3, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
    hr.2.2.2.2.2, ite_false]

/-- The registers a block writes. -/
abbrev regs : List Reg := [.x20, .x21, .x22, .x23, .x24, .x25, .x27, .x28, .x30]

/-- The clamped key, as a number. -/
abbrev rval (s : State) : Nat := (rword s r0Off).toNat + 2 ^ 64 * (rword s r1Off).toNat

theorem block_eq : block = addBlock ++ (mulR0 ++ (mulR1 ++ reduce)) := by
  simp only [block, List.append_assoc]

theorem rword_keeps {rs : List Reg} {s s' : State} (h : Keeps rs s s') (h0 : Reg.x0 ∉ rs)
    (d : Nat) : rword s' d = rword s d := by
  simp only [rword, h.1 _ h0, h.2.1]

theorem block_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 8) 8)
    (hk0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 r0Off) 8)
    (hk1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 r1Off) 8)
    (hr0 : (rword s r0Off).toNat < 2 ^ 60) (hr1 : (rword s r1Off).toNat < 2 ^ 60)
    (hh2 : (s.gpr .x23).toNat ≤ 4) :
    WP isa (.block block) s fun s' =>
      hval s' % P = ((hval s + (word s.mem (s.gpr .x20) 0 + 2 ^ 64 * word s.mem (s.gpr .x20) 8 +
        2 ^ 128)) * rval s) % P ∧ (s'.gpr .x23).toNat ≤ 4 ∧
      s'.gpr .x20 = s.gpr .x20 + 16#64 ∧ Keeps regs s s' := by
  rw [block_eq]
  refine WP.block_append (WP.mono (addBlock_ok s h0 h8) fun s₁ ⟨e₁, k₁⟩ => ?_)
  have k0₁ : s₁.gpr .x0 = s.gpr .x0 := k₁.gpr'
  have k20₁ : s₁.gpr .x20 = s.gpr .x20 := k₁.gpr'
  have rw₁ := rword_keeps k₁ (by decide)
  refine WP.block_append (WP.mono (mulR0_ok s₁ (by rw [k₁.2.2.1, k₁.2.2.2, k0₁]; exact hk0))
    fun s₂ ⟨e₂, k₂⟩ => ?_)
  have rw₂ := rword_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (mulR1_ok s₂ (by
      rw [k₂.2.2.1, k₂.2.2.2, k₁.2.2.1, k₁.2.2.2, k₂.gpr', k0₁]; exact hk1))
    fun s₃ ⟨e₃, k₃⟩ => ?_)
  refine WP.mono (reduce_ok s₃) fun s₄ ⟨e₄, p₄, k₄⟩ => ?_
  -- The block added.
  have g0 := (s.gpr .x21).isLt; have g1 := (s.gpr .x22).isLt
  have hw0 := (s.mem.readW (s.gpr .x20 + BitVec.ofNat 64 0) 64).isLt
  have hw8 := (s.mem.readW (s.gpr .x20 + BitVec.ofNat 64 8) 64).isLt
  have e₁ := e₁ (by simp only [word, hval]; omega_using [hh2, g0, g1, hw0, hw8])
  have a0 := (s₁.gpr .x21).isLt; have a1 := (s₁.gpr .x22).isLt
  have a2 : (s₁.gpr .x23).toNat ≤ 6 := by
    simp only [word, hval] at e₁; omega_using [e₁, hh2, g0, g1, hw0, hw8, a0, a1]
  -- The products.
  rw [rw₁] at e₂
  obtain ⟨e₂, t2₂⟩ := e₂ hr0 a2
  have hv₂ : hval s₂ = hval s₁ := by
    simp only [hval, k₂.gpr' (r := .x21), k₂.gpr' (r := .x22), k₂.gpr' (r := .x23)]
  have x23₂ : s₂.gpr .x23 = s₁.gpr .x23 := k₂.gpr'
  rw [rw₂, rw₁, hv₂, x23₂] at e₃
  have e₃ := e₃ hr1 a2 t2₂
  have x25₃ : s₃.gpr .x25 = s₂.gpr .x25 := k₃.gpr'
  -- `t = h r`, below `7 ⋅ 2²⁵²`.
  have ht : (s₃.gpr .x25).toNat + 2 ^ 64 * (s₃.gpr .x27).toNat + 2 ^ 128 * (s₃.gpr .x28).toNat +
      2 ^ 192 * (s₃.gpr .x30).toNat = hval s₁ * rval s := by
    simp only [rval, x25₃]
    rw [Nat.mul_add, ← Nat.mul_assoc (hval s₁), Nat.mul_comm (hval s₁) (2 ^ 64), Nat.mul_assoc]
    omega_using [e₂, e₃]
  have hb₁ : hval s₁ < 7 * 2 ^ 128 := by simp only [hval]; omega_using [a0, a1, a2]
  have hR : rval s < 2 ^ 124 := by simp only [rval]; omega_using [hr0, hr1]
  have hbt : hval s₁ * rval s < 7 * 2 ^ 252 := by
    have := Nat.mul_lt_mul'' hb₁ hR; omega_using [this]
  have t0 := (s₃.gpr .x25).isLt; have t1 := (s₃.gpr .x27).isLt; have t2 := (s₃.gpr .x28).isLt
  have e₄ := e₄ (by omega_using [ht, hbt, t0, t1, t2])
  have w0 := (s₄.gpr .x21).isLt; have w1 := (s₄.gpr .x22).isLt
  refine ⟨?_, ?_, ?_, (k₁.trans (k₂.trans (k₃.trans k₄))).mono (by decide)⟩
  · rw [e₄, ← e₁, ← ht]
    rw [show (s₃.gpr .x25).toNat + 2 ^ 64 * (s₃.gpr .x27).toNat + 2 ^ 128 * (s₃.gpr .x28).toNat +
        2 ^ 192 * (s₃.gpr .x30).toNat =
        ((s₃.gpr .x25).toNat + 2 ^ 64 * (s₃.gpr .x27).toNat + 2 ^ 128 * ((s₃.gpr .x28).toNat % 4) +
          5 * ((s₃.gpr .x28).toNat / 4 + 2 ^ 62 * (s₃.gpr .x30).toNat)) +
        P * ((s₃.gpr .x28).toNat / 4 + 2 ^ 62 * (s₃.gpr .x30).toNat) by
      simp only [P]; omega_using [], Nat.add_mul_mod_self_left]
  · simp only [hval] at e₄
    omega_using [e₄, ht, hbt, t0, t1, t2, w0, w1]
  · rw [p₄, k₃.gpr', k₂.gpr', k20₁]

/-- A partially reduced accumulator for the clamped key `R`: `h ≡ acc` and
`h₂ ≤ 4`, with the key's words below `2⁶⁰`. -/
structure Acc (R acc : Nat) (s : State) : Prop where
  h : hval s % P = acc % P
  h2 : (s.gpr .x23).toNat ≤ 4
  key : rval s = R
  k0 : (rword s r0Off).toNat < 2 ^ 60
  k1 : (rword s r1Off).toNat < 2 ^ 60

/-- A block absorbed: the accumulator of the message followed by the 16
bytes at `x20`. -/
theorem block_absorb {R acc : Nat} (s : State) (ha : Acc R acc s)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 8) 8)
    (hk0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 r0Off) 8)
    (hk1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 r1Off) 8) :
    WP isa (.block block) s fun s' =>
      Acc R (Poly1305.absorbAll R acc (Spec.Poly1305.bytesAt s.mem (s.gpr .x20) 16)) s' ∧
      s'.gpr .x20 = s.gpr .x20 + 16#64 ∧ Keeps regs s s' := by
  refine WP.mono (block_ok s h0 h8 hk0 hk1 ha.k0 ha.k1 ha.h2) fun s' ⟨e, b, p, k⟩ => ?_
  have rw' := rword_keeps k (by decide)
  refine ⟨⟨?_, b, ?_, by rw [rw']; exact ha.k0, by rw [rw']; exact ha.k1⟩, p, k⟩
  · have hm : word s.mem (s.gpr .x20) 0 + 2 ^ 64 * word s.mem (s.gpr .x20) 8 + 2 ^ 128 =
        Spec.Poly1305.leNum (Spec.Poly1305.bytesAt s.mem (s.gpr .x20) 16 ++ [0x01]) := by
      rw [Poly1305.leNum_append, Poly1305.length_bytesAt, Poly1305.AArch64.leNum_key]
      rfl
    have hb1 : 0 < (Spec.Poly1305.bytesAt s.mem (s.gpr .x20) 16).length := by
      rw [Poly1305.length_bytesAt]; decide
    have hb2 : (Spec.Poly1305.bytesAt s.mem (s.gpr .x20) 16).length ≤ 16 := by
      rw [Poly1305.length_bytesAt]
    rw [e, hm, ha.key, Poly1305.absorbAll_block hb1 hb2, Nat.mod_mod,
      Poly1305.AArch64.mod_step ha.h, Nat.mod_mod]
  · simp only [rval, rw']; exact ha.key

end VG.Proof.ChaCha20Poly1305.AArch64.Poly

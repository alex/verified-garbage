import VerifiedGarbage.Impl.X25519.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X25519.Field

/-!
# X25519 on x86-64: the steps of the field arithmetic

Untrusted: everything here is checked by Lean. The small blocks the field
operations are made of (see `Impl/X25519/X86_64.lean`), each run
symbolically once, for any registers: a multiply-accumulate step, and the
carry of a 38-fold into four words.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- The registers of `s'` are those of `s` but for `rs`, and memory and the
regions are unchanged. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂) (h₂ : Keeps rs s₂ s₃) :
    Keeps rs s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem toNat_ofBool (c : Bool) : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by
  cases c <;> rfl

theorem se0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide

/-- The arithmetic of a multiply-accumulate step: the product's halves, the
carry word `c` added to the low half, and the sum added to `t`, each carry
going into the high half, which never overflows. -/
theorem step_arith (a v c t : BitVec 64) :
    let p := a.toNat * v.toNat
    let lo : BitVec 64 := BitVec.ofNat 64 p
    let hi : BitVec 64 := BitVec.ofNat 64 (p / 2 ^ 64)
    let r := lo + c
    let d := hi + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ lo.toNat + c.toNat))).setWidth 64
    (t + r).toNat + 2 ^ 64 *
        (d + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ t.toNat + r.toNat))).setWidth 64).toNat =
      t.toNat + c.toNat + a.toNat * v.toNat := by
  intro p lo hi r d
  have ha := a.isLt; have hv := v.isLt; have hc := c.isLt; have ht := t.isLt
  have hp : p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hlo : lo.toNat = p % 2 ^ 64 := BitVec.toNat_ofNat _ _
  have hhi : hi.toNat = p / 2 ^ 64 := by
    simp only [hi, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv : p / 2 ^ 64 ≤ 2 ^ 64 - 2 := by omega
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [r, d, BitVec.toNat_add, toNat_ofBool, hz, Nat.add_zero, hlo, hhi] at *
  by_cases h1 : 2 ^ 64 ≤ p % 2 ^ 64 + c.toNat <;>
  simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
  [by_cases h2 : 2 ^ 64 ≤ t.toNat + (p % 2 ^ 64 + c.toNat) % 2 ^ 64;
    by_cases h2 : 2 ^ 64 ≤ t.toNat + (p % 2 ^ 64 + c.toNat) % 2 ^ 64] <;>
  simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- A multiply-accumulate step: `t:c = t + c + ai · src`. -/
theorem mulStep_ok (s : State) {t c ai : Reg} {src : Src} {v : BitVec 64}
    (hsrc : readSrc s src = some v) (ht : t ≠ .rax) (ht' : t ≠ .rdx) (hc : c ≠ .rax)
    (hc' : c ≠ .rdx) (ha : ai ≠ .rax) (htc : t ≠ c) :
    WP isa (.block (mulStep t c ai src)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr t).toNat + (s.gpr c).toNat + (s.gpr ai).toNat * v.toNat ∧
      Keeps [t, c, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [mulStep, runBlock_cons, exec, hsrc, Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ha, hc, ht, htc, hc', ht',
    Ne.symm htc, Ne.symm ht', ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := step_arith (s.gpr ai) v (s.gpr c) (s.gpr t)
    simp only at e
    rw [Nat.mul_comm (s.gpr ai).toNat] at e ⊢
    exact e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]

/-- The halves of a product of two words (`mul`, `mulx`): `lo + 2⁶⁴ hi`. -/
theorem mulx_arith (d v : BitVec 64) :
    (BitVec.ofNat 64 (d.toNat * v.toNat)).toNat +
        2 ^ 64 * (BitVec.ofNat 64 (d.toNat * v.toNat / 2 ^ 64)).toNat = d.toNat * v.toNat := by
  have hd := d.isLt; have hv := v.isLt
  have hp : d.toNat * v.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hd hv
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega)]
  omega

/-! ## Carry chains -/

theorem add_carry (a b : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat = a.toNat + b.toNat := by
  have := a.isLt; have := b.isLt
  rw [BitVec.toNat_add]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat +
        2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, toNat_ofBool]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem sub_borrow (a b : BitVec 64) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat)).toNat := by
  have := a.isLt; have := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem sbb_borrow (a b : BitVec 64) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 64).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  rw [BitVec.toNat_sub, BitVec.toNat_sub, toNat_ofBool]
  by_cases h : a.toNat < b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- The value of four words. -/
abbrev val4 (a0 a1 a2 a3 : BitVec 64) : Nat :=
  a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat

/-- `add`, then three `adc`: the sum of two four-word numbers and the carry
out. -/
theorem chain_add (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    let c0 := decide (2 ^ 64 ≤ a0.toNat + b0.toNat)
    let c1 := decide (2 ^ 64 ≤ a1.toNat + b1.toNat + c0.toNat)
    let c2 := decide (2 ^ 64 ≤ a2.toNat + b2.toNat + c1.toNat)
    let c3 := decide (2 ^ 64 ≤ a3.toNat + b3.toNat + c2.toNat)
    val4 (a0 + b0) (a1 + b1 + (BitVec.ofBool c0).setWidth 64) (a2 + b2 + (BitVec.ofBool c1).setWidth 64)
        (a3 + b3 + (BitVec.ofBool c2).setWidth 64) + 2 ^ 256 * c3.toNat =
      val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 := by
  have e0 := add_carry a0 b0
  have e1 := adc_carry a1 b1 (decide (2 ^ 64 ≤ a0.toNat + b0.toNat))
  have e2 := adc_carry a2 b2 (decide (2 ^ 64 ≤ a1.toNat + b1.toNat +
    (decide (2 ^ 64 ≤ a0.toNat + b0.toNat)).toNat))
  have e3 := adc_carry a3 b3 (decide (2 ^ 64 ≤ a2.toNat + b2.toNat + (decide (2 ^ 64 ≤ a1.toNat +
    b1.toNat + (decide (2 ^ 64 ≤ a0.toNat + b0.toNat)).toNat)).toNat))
  simp only [val4]
  omega

/-- `sub`, then three `sbb`: the difference of two four-word numbers, plus
`2²⁵⁶` if it borrows. -/
theorem chain_sub (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    let c0 := decide (a0.toNat < b0.toNat)
    let c1 := decide (a1.toNat < b1.toNat + c0.toNat)
    let c2 := decide (a2.toNat < b2.toNat + c1.toNat)
    let c3 := decide (a3.toNat < b3.toNat + c2.toNat)
    val4 (a0 - b0) (a1 - b1 - (BitVec.ofBool c0).setWidth 64) (a2 - b2 - (BitVec.ofBool c1).setWidth 64)
        (a3 - b3 - (BitVec.ofBool c2).setWidth 64) + val4 b0 b1 b2 b3 =
      val4 a0 a1 a2 a3 + 2 ^ 256 * c3.toNat := by
  have e0 := sub_borrow a0 b0
  have e1 := sbb_borrow a1 b1 (decide (a0.toNat < b0.toNat))
  have e2 := sbb_borrow a2 b2 (decide (a1.toNat < b1.toNat + (decide (a0.toNat < b0.toNat)).toNat))
  have e3 := sbb_borrow a3 b3 (decide (a2.toNat < b2.toNat +
    (decide (a1.toNat < b1.toNat + (decide (a0.toNat < b0.toNat)).toNat)).toNat))
  simp only [val4]
  omega

/-- `sbb x, x` then `and 38`: 38 if the carry was set, else 0. -/
theorem mask38 (x : BitVec 64) (c : Bool) :
    ((x - x - (BitVec.ofBool c).setWidth 64) &&& BitVec.signExtend 64 (38 : BitVec 32)).toNat =
      38 * c.toNat := by
  cases c <;> simp only [BitVec.sub_self] <;> decide

open VG.Spec.X25519 (P) in
/-- `carry38`: `r8–r11 + rax`, with the carry out folded in as 38, is the
same number modulo `p`, if `rax < 2⁵⁸`. -/
theorem carry38_ok (s : State) (hx : (s.gpr .rax).toNat < 2 ^ 58) :
    WP isa (.block carry38) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + (s.gpr .rax).toNat) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [carry38, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .rax) 0 0 0
    simp only at e
    generalize hc : decide (2 ^ 64 ≤ (s.gpr Reg.r11).toNat + BitVec.toNat 0 +
      (decide (2 ^ 64 ≤ (s.gpr Reg.r10).toNat + BitVec.toNat 0 +
        (decide (2 ^ 64 ≤ (s.gpr Reg.r9).toNat + BitVec.toNat 0 +
          (decide (2 ^ 64 ≤ (s.gpr Reg.r8).toNat + (s.gpr Reg.rax).toNat)).toNat)).toNat)).toNat) = c at e ⊢
    simp only [val4] at e ⊢
    rw [BitVec.toNat_add (s.gpr .r8 + s.gpr .rax), mask38]
    have h0 := (s.gpr .r8 + s.gpr .rax).isLt
    have h1 := (s.gpr .r9).isLt; have h2 := (s.gpr .r10).isLt; have h3 := (s.gpr .r11).isLt
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    simp only [hz] at e ⊢
    have hb : (s.gpr .r8 + s.gpr .rax).toNat + 38 * c.toNat < 2 ^ 64 := by
      cases c
      · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]; exact h0
      · simp only [Bool.toNat_true, Nat.mul_one] at e ⊢
        omega
    rw [Nat.mod_eq_of_lt hb]
    have hc := Bool.toNat_le c
    simp only [P]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

end VG.Proof.X25519.X86_64

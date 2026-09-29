import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Impl.Poly1305.X86_64
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset

section

section

/-!
# Poly1305 on x86-64: the arithmetic of a block

Untrusted: everything here is checked by Lean. The numbers the code computes
while absorbing a block (see `Impl/Poly1305/X86_64.lean`), as natural
numbers: the accumulator `h = h0 + 2⁶⁴ h1 + 2¹²⁸ h2`, the clamped
`r = r0 + 2⁶⁴ r1` with `r1 = 4 q`, and `s1 = 5 q`. The products are named
(`h0 * r0`, …) so that `omega` treats them as atoms.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86_64

open VG.Spec.Poly1305 (P)

theorem mul_lt {a b c d : Nat} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  Nat.mul_lt_mul_of_lt_of_lt h₁ h₂

theorem mul_le_lt {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c < d) : a * c ≤ b * d :=
  Nat.mul_le_mul h₁ (Nat.le_of_lt h₂)

/-- The bounds that make every sum of products fit its registers. -/
theorem absorb_bounds {h0 h1 h2 r0 q : Nat} (hh0 : h0 < 2 ^ 64) (hh1 : h1 < 2 ^ 64) (hh2 : h2 ≤ 6)
    (hr0 : r0 < 2 ^ 60) (hq : q < 2 ^ 58) :
    h0 * r0 < 2 ^ 124 ∧ h1 * (5 * q) < 2 ^ 125 ∧ h0 * (4 * q) < 2 ^ 124 ∧ h1 * r0 < 2 ^ 124 ∧
      h2 * (5 * q) < 2 ^ 64 ∧ h2 * r0 ≤ 6 * r0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := mul_lt hh0 hr0; omega
  · have := mul_lt hh1 (show 5 * q < 5 * 2 ^ 58 by omega); omega
  · have := mul_lt hh0 (show 4 * q < 4 * 2 ^ 58 by omega); omega
  · have := mul_lt hh1 hr0; omega
  · have := mul_le_lt hh2 (show 5 * q < 5 * 2 ^ 58 by omega); omega
  · exact Nat.mul_le_mul_right _ hh2

/-- `(h0 + 2⁶⁴ h1 + 2¹²⁸ h2) (r0 + 2⁶⁴ 4 q)`, expanded into the named products. -/
theorem expand (h0 h1 h2 r0 q : Nat) :
    (h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2) * (r0 + 2 ^ 64 * (4 * q)) =
      h0 * r0 + 2 ^ 64 * (h0 * (4 * q)) + 2 ^ 64 * (h1 * r0) + 2 ^ 130 * (h1 * q) +
        2 ^ 128 * (h2 * r0) + 2 ^ 194 * (h2 * q) := by
  grind

/-- Absorbing a block: `x = x0 + 2⁶⁴ x1 = h0 r0 + h1 s1`, `y = y0 + 2⁶⁴ y1 =
h0 r1 + h1 r0 + h2 s1`, `u0 + 2⁶⁴ c1 = y0 + x1`, the top word `t = y1 + h2 r0 +
c1`, and the result `w = x0 + 5 ⌊t / 4⌋ + 2⁶⁴ u0 + 2¹²⁸ (t mod 4)` in three
words: `w ≡ h r` modulo `p`, and `w2 ≤ 4`. -/
theorem absorb_arith {h0 h1 h2 r0 q x0 x1 y0 y1 u0 c1 w0 w1 w2 : Nat}
    (hh0 : h0 < 2 ^ 64) (hh1 : h1 < 2 ^ 64) (hh2 : h2 ≤ 6) (hr0 : r0 < 2 ^ 60) (hq : q < 2 ^ 58)
    (hx : x0 + 2 ^ 64 * x1 = h0 * r0 + h1 * (5 * q)) (hx0 : x0 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 = h0 * (4 * q) + h1 * r0 + h2 * (5 * q))
    (hu : u0 + 2 ^ 64 * c1 = y0 + x1) (hu0 : u0 < 2 ^ 64)
    (hw : w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 =
      x0 + 5 * ((y1 + h2 * r0 + c1) / 4) + 2 ^ 64 * u0 + 2 ^ 128 * ((y1 + h2 * r0 + c1) % 4))
    (hw0 : w0 < 2 ^ 64) (hw1 : w1 < 2 ^ 64) :
    (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) % P =
      ((h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2) * (r0 + 2 ^ 64 * (4 * q))) % P ∧ w2 ≤ 4 := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := absorb_bounds hh0 hh1 hh2 hr0 hq
  have e5 : h1 * (5 * q) = 5 * (h1 * q) := Nat.mul_left_comm _ _ _
  have e4 : h0 * (4 * q) = 4 * (h0 * q) := Nat.mul_left_comm _ _ _
  have e5' : h2 * (5 * q) = 5 * (h2 * q) := Nat.mul_left_comm _ _ _
  rw [expand]
  refine ⟨?_, ?_⟩
  · rw [show h0 * r0 + 2 ^ 64 * (h0 * (4 * q)) + 2 ^ 64 * (h1 * r0) + 2 ^ 130 * (h1 * q) +
        2 ^ 128 * (h2 * r0) + 2 ^ 194 * (h2 * q) =
        (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) +
          P * ((y1 + h2 * r0 + c1) / 4 + h1 * q + 2 ^ 64 * (h2 * q)) by
      simp only [P]; omega, Nat.add_mul_mod_self_left]
  · omega

/-- Adding a block `m0 + 2⁶⁴ m1 + 2¹²⁸ pad` to `h` with `h2 ≤ 4`: the result's
top word is at most 6. -/
theorem add_arith {h0 h1 h2 m0 m1 pad w0 w1 w2 : Nat} (hh0 : h0 < 2 ^ 64) (hh1 : h1 < 2 ^ 64)
    (hh2 : h2 ≤ 4) (hm0 : m0 < 2 ^ 64) (hm1 : m1 < 2 ^ 64) (hpad : pad ≤ 1)
    (hw : w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 =
      h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2 + (m0 + 2 ^ 64 * m1 + 2 ^ 128 * pad))
    (hw0 : w0 < 2 ^ 64) (hw1 : w1 < 2 ^ 64) : w2 ≤ 6 := by
  omega

end VG.Proof.Poly1305.X86_64

end

/-!
# Poly1305 on x86-64: the steps of a block

Untrusted: everything here is checked by Lean. Each lemma runs a few
instructions symbolically and states their effect on the numbers in the
registers.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64

/-- Two states agree except on the registers `rs`, in memory and regions. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem toNat_mul_lo (a b : BitVec 64) :
    (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := by
  have := mul_lt a.isLt b.isLt
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega)]
  omega

set_option simprocs false in
theorem mulTo_ok {lo hi a b : Reg} (s : State) (hb : b ≠ .rax) (hlo : lo ≠ .rdx)
    (hlh : lo ≠ hi) :
    WP isa (.block (mulTo lo hi a b)) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr a).toNat * (s.gpr b).toNat ∧
      Keeps [lo, hi, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [mulTo, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul, State.setReg,
    State.setFlags, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp (config := {decide := true}) only [ite_true, hlh, hlo.symm, ite_false, hb]
    exact toNat_mul_lo _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

theorem carry_toNat (c : Bool) :
    ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by
  cases c <;> rfl

/-- An addition with carry into a second word, as numbers, when the sum fits. -/
theorem add_adc_toNat (a b c d : BitVec 64)
    (h : a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat) < 2 ^ 128) :
    (a + b).toNat + 2 ^ 64 * (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).toNat =
      a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat) := by
  simp only [BitVec.toNat_add, carry_toNat]
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  by_cases h2 : 2 ^ 64 ≤ a.toNat + b.toNat <;> simp only [h2, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

set_option simprocs false in
theorem mulAdd_ok {lo hi a b : Reg} (s : State) (hb : b ≠ .rax) (hlo : lo ≠ .rdx) (hlo' : lo ≠ .rax)
    (hhi : hi ≠ .rdx) (hhi' : hi ≠ .rax) (hlh : lo ≠ hi) :
    WP isa (.block (mulAdd lo hi a b)) s fun s' =>
      ((s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr b).toNat < 2 ^ 128 →
        (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat =
          (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr b).toNat) ∧
      Keeps [lo, hi, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mulAdd, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execMul, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, hb, hlo, hlo', hhi,
    hhi', hlh, hlo.symm, hlh.symm]
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := toNat_mul_lo (s.gpr a) (s.gpr b)
    rw [add_adc_toNat _ _ _ _ (by have := (s.gpr hi).isLt; omega)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

/-- Three words added with carries, as numbers, when the sum fits. -/
theorem add3_toNat (a b c d e f : BitVec 64)
    (h : a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat) + 2 ^ 128 * (e.toNat + f.toNat) < 2 ^ 192) :
    (a + b).toNat +
      2 ^ 64 * (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).toNat +
      2 ^ 128 * (e + f + (BitVec.ofBool (decide (2 ^ 64 ≤ c.toNat + d.toNat +
        (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat))).setWidth 64).toNat =
    a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat) + 2 ^ 128 * (e.toNat + f.toNat) := by
  simp only [BitVec.toNat_add]
  rw [carry_toNat, carry_toNat]
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  have he := e.isLt; have hf := f.isLt
  by_cases h1 : 2 ^ 64 ≤ a.toNat + b.toNat <;>
  simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
  [by_cases h2 : 2 ^ 64 ≤ c.toNat + d.toNat + 1; by_cases h2 : 2 ^ 64 ≤ c.toNat + d.toNat + 0] <;>
  simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

set_option simprocs false in
/-- `h2 * r0`, which fits one word. -/
theorem mulSmall_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rbp), .mul .r8]) s fun s' =>
      ((s.gpr .rbp).toNat * (s.gpr .r8).toNat < 2 ^ 64 →
        (s'.gpr .rax).toNat = (s.gpr .rbp).toNat * (s.gpr .r8).toNat) ∧ Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execMul, State.setReg, State.setFlags, Option.map_some, Option.some.injEq,
    exists_eq_left', ite_true, ite_false]
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]

set_option simprocs false in
theorem addPair_ok (s : State) :
    WP isa (.block [.alu .add .r14 (.reg .r13), .alu .adc .r15 (.reg .rax)]) s fun s' =>
      ((s.gpr .r14).toNat + (s.gpr .r13).toNat + 2 ^ 64 * ((s.gpr .r15).toNat + (s.gpr .rax).toNat) <
          2 ^ 128 →
        (s'.gpr .r14).toNat + 2 ^ 64 * (s'.gpr .r15).toNat =
          (s.gpr .r14).toNat + (s.gpr .r13).toNat + 2 ^ 64 * ((s.gpr .r15).toNat + (s.gpr .rax).toNat)) ∧
      Keeps [.r14, .r15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false]
  refine ⟨add_adc_toNat _ _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

theorem se3 : BitVec.signExtend 64 (3 : BitVec 32) = 3 := by decide
theorem se0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

theorem and3_toNat (x : BitVec 64) : (x &&& 3).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 2

set_option simprocs false in
/-- Splitting the top word `t` (in `r15`) into `t mod 4` (in `rbp`) and `5 ⌊t / 4⌋`
(in `rax`), and moving the low words into `r11, rbx`. -/
theorem split_ok (s : State) :
    WP isa (.block [.mov .r11 (.reg .r12), .mov .rbx (.reg .r14), .mov .rbp (.reg .r15),
      .alu .and .rbp (.imm 3), .mov .rax (.reg .r15), .alu .sub .rax (.reg .rbp),
      .shift .shr .r15 2, .alu .add .rax (.reg .r15)]) s fun s' =>
      s'.gpr .r11 = s.gpr .r12 ∧ s'.gpr .rbx = s.gpr .r14 ∧
      (s'.gpr .rbp).toNat = (s.gpr .r15).toNat % 4 ∧
      ((s.gpr .r15).toNat < 2 ^ 63 → (s'.gpr .rax).toNat = 5 * ((s.gpr .r15).toNat / 4)) ∧
      Keeps [.r11, .rbx, .rbp, .rax, .r15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, execShift, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, se3]
  refine ⟨trivial, trivial, and3_toNat _, fun ht => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h3 := and3_toNat (s.gpr .r15)
    have hle : s.gpr .r15 &&& 3 ≤ s.gpr .r15 := by
      rw [BitVec.le_def, h3]; exact Nat.mod_le _ _
    rw [BitVec.toNat_add, BitVec.toNat_sub_of_le hle, h3, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]

set_option simprocs false in
/-- Adding `rax` into `r11, rbx, rbp`, with carries. -/
theorem addLow_ok (s : State) :
    WP isa (.block [.alu .add .r11 (.reg .rax), .alu .adc .rbx (.imm 0), .alu .adc .rbp (.imm 0)]) s
      fun s' =>
      ((s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rbx).toNat +
          2 ^ 128 * (s.gpr .rbp).toNat < 2 ^ 192 →
        (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
          (s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rbx).toNat +
            2 ^ 128 * (s.gpr .rbp).toNat) ∧
      Keeps [.r11, .rbx, .rbp] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, se0]
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [add3_toNat _ _ _ _ _ _ (by rw [hz]; omega), hz]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-- The two words of the block at `p`. -/
abbrev word (m : Mem) (p : Addr) (d : Nat) : Nat := (m.readW (p + BitVec.ofInt 64 (d : Int)) 64).toNat

set_option simprocs false in
/-- `h += m + pad · 2¹²⁸` for the block `m` at `b + d`. -/
theorem addBlockAt_ok (s : State) {b : Reg} (hb : b ≠ .r11) {d : Nat} {pad : BitVec 32}
    (hpad : pad = 0 ∨ pad = 1)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (d : Int)) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 ((d + 8 : Nat) : Int)) 8) :
    WP isa (.block (addBlockAt b d pad)) s fun s' =>
      ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat +
          (word s.mem (s.gpr b) d + 2 ^ 64 * word s.mem (s.gpr b) (d + 8) + 2 ^ 128 * pad.toNat) <
          2 ^ 192 →
        (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
          (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat +
            (word s.mem (s.gpr b) d + 2 ^ 64 * word s.mem (s.gpr b) (d + 8) + 2 ^ 128 * pad.toNat)) ∧
      Keeps [.r11, .rbx, .rbp] s s' := by
  have hp : (pad.signExtend 64).toNat = pad.toNat := by rcases hpad with rfl | rfl <;> rfl
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addBlockAt, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, State.load64, ea_at, hb, h0, h8,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false]
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [word] at hlt ⊢
    rw [add3_toNat _ _ _ _ _ _ (by rw [hp]; omega), hp]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2]

end VG.Proof.Poly1305.X86_64

end

section

/-!
# Poly1305 on x86-64: absorbing a block

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P)

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

/-- The registers `absorb` writes. -/
abbrev absorbRegs : List Reg := [.r11, .rbx, .rbp, .rax, .rdx, .r12, .r13, .r14, .r15]

theorem carry_eq : carry =
    ([.alu .add .r14 (.reg .r13), .alu .adc .r15 (.reg .rax)] : List Instr) ++
    (([.mov .r11 (.reg .r12), .mov .rbx (.reg .r14), .mov .rbp (.reg .r15),
      .alu .and .rbp (.imm 3), .mov .rax (.reg .r15), .alu .sub .rax (.reg .rbp),
      .shift .shr .r15 2, .alu .add .rax (.reg .r15)] : List Instr) ++
    ([.alu .add .r11 (.reg .rax), .alu .adc .rbx (.imm 0), .alu .adc .rbp (.imm 0)] : List Instr)) := rfl

theorem absorbAt_eq (b : Reg) (d : Nat) (pad : BitVec 32) : absorbAt b d pad =
    addBlockAt b d pad ++ (mulTo .r12 .r13 .r11 .r8 ++ (mulAdd .r12 .r13 .rbx .r10 ++
    (mulTo .r14 .r15 .r11 .r9 ++ (mulAdd .r14 .r15 .rbx .r8 ++ (mulAdd .r14 .r15 .rbp .r10 ++
    (([.mov .rax (.reg .rbp), .mul .r8] : List Instr) ++ carry)))))) := by
  simp only [absorbAt, products, List.append_assoc]

/-- The accumulator in `r11, rbx, rbp`. -/
abbrev hval (s : State) : Nat :=
  (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat

/-- Absorbing the block at `b + d`: from `h` with `h2 ≤ 4`, the clamped `r0, r1 = 4 q`
in `r8, r9` and `s1 = 5 q` in `r10`, the new `h` is congruent to
`(h + m + pad · 2¹²⁸) r` modulo `p`, and its `h2` is at most 4. -/
theorem absorbAt_ok (s : State) {b : Reg} (hb : b ≠ .r11) {d : Nat} {pad : BitVec 32}
    (hpad : pad = 0 ∨ pad = 1) {q : Nat}
    (hr0 : (s.gpr .r8).toNat < 2 ^ 60) (hr1 : (s.gpr .r9).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s.gpr .r10).toNat = 5 * q)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (d : Int)) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 ((d + 8 : Nat) : Int)) 8) :
    WP isa (.block (absorbAt b d pad)) s fun s' =>
      ((s.gpr .rbp).toNat ≤ 4 →
        hval s' % P = ((hval s + (word s.mem (s.gpr b) d + 2 ^ 64 * word s.mem (s.gpr b) (d + 8) +
          2 ^ 128 * pad.toNat)) * ((s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r9).toNat)) % P ∧
        (s'.gpr .rbp).toNat ≤ 4) ∧ Keeps absorbRegs s s' := by
  rw [absorbAt_eq, carry_eq]
  refine WP.block_append (WP.mono (addBlockAt_ok s hb hpad h0 h8) fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (mulTo_ok s₁ (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (mulAdd_ok s₂ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨e₃, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (mulTo_ok s₃ (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (mulAdd_ok s₄ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨e₅, k₅⟩ => ?_)
  refine WP.block_append (WP.mono (mulAdd_ok s₅ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨e₆, k₆⟩ => ?_)
  refine WP.block_append (WP.mono (mulSmall_ok s₆) fun s₇ ⟨e₇, k₇⟩ => ?_)
  refine WP.block_append (WP.mono (addPair_ok s₇) fun s₈ ⟨e₈, k₈⟩ => ?_)
  refine WP.block_append (WP.mono (split_ok s₈) fun s₉ ⟨f₁, f₂, f₃, f₄, k₉⟩ => ?_)
  refine WP.mono (addLow_ok s₉) fun s₁₀ ⟨e₁₀, k₁₀⟩ => ?_
  refine ⟨fun hh2 => ?_, (k₁.trans ((((((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans
    k₈).trans k₉).trans k₁₀)).mono (by decide)⟩
  have hp1 : pad.toNat ≤ 1 := by rcases hpad with rfl | rfl <;> decide
  have hw0 := (s.mem.readW (s.gpr b + BitVec.ofInt 64 (d : Int)) 64).isLt
  have hw8 := (s.mem.readW (s.gpr b + BitVec.ofInt 64 ((d + 8 : Nat) : Int)) 64).isLt
  have g0 := (s.gpr .r11).isLt; have g1 := (s.gpr .rbx).isLt
  -- h += m
  have e₁ := e₁ (by simp only [word]; omega)
  have a0 := (s₁.gpr .r11).isLt; have a1 := (s₁.gpr .rbx).isLt
  have a2 : (s₁.gpr .rbp).toNat ≤ 6 := add_arith g0 g1 hh2 hw0 hw8 hp1 e₁ a0 a1
  have r8₁ : s₁.gpr .r8 = s.gpr .r8 := k₁.gpr'
  have r9₁ : s₁.gpr .r9 = s.gpr .r9 := k₁.gpr'
  have r10₁ : s₁.gpr .r10 = s.gpr .r10 := k₁.gpr'
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := absorb_bounds a0 a1 a2 hr0 hq
  -- x = h0 r0
  rw [r8₁] at e₂
  have rbx₂ : s₂.gpr .rbx = s₁.gpr .rbx := k₂.gpr'
  have r10₂ : s₂.gpr .r10 = s.gpr .r10 := k₂.gpr'.trans r10₁
  -- x += h1 s1
  rw [rbx₂, r10₂, hs1] at e₃
  have e₃ := e₃ (by omega)
  rw [e₂] at e₃
  have k₃' := k₂.trans k₃
  have r11₃ : s₃.gpr .r11 = s₁.gpr .r11 := k₃'.gpr'
  have r9₃ : s₃.gpr .r9 = s.gpr .r9 := k₃'.gpr'.trans r9₁
  -- y = h0 r1
  rw [r11₃, r9₃, hr1] at e₄
  have k₄' := k₃'.trans k₄
  have rbx₄ : s₄.gpr .rbx = s₁.gpr .rbx := k₄'.gpr'
  have r8₄ : s₄.gpr .r8 = s.gpr .r8 := k₄'.gpr'.trans r8₁
  -- y += h1 r0
  rw [rbx₄, r8₄] at e₅
  have e₅ := e₅ (by omega)
  rw [e₄] at e₅
  have k₅' := k₄'.trans k₅
  have rbp₅ : s₅.gpr .rbp = s₁.gpr .rbp := k₅'.gpr'
  have r10₅ : s₅.gpr .r10 = s.gpr .r10 := k₅'.gpr'.trans r10₁
  -- y += h2 s1
  rw [rbp₅, r10₅, hs1] at e₆
  have e₆ := e₆ (by omega)
  rw [e₅] at e₆
  have k₆' := k₅'.trans k₆
  have rbp₆ : s₆.gpr .rbp = s₁.gpr .rbp := k₆'.gpr'
  have r8₆ : s₆.gpr .r8 = s.gpr .r8 := k₆'.gpr'.trans r8₁
  -- h2 r0
  rw [rbp₆, r8₆] at e₇
  have e₇ := e₇ (by omega)
  have r14₇ : s₇.gpr .r14 = s₆.gpr .r14 := k₇.gpr'
  have r15₇ : s₇.gpr .r15 = s₆.gpr .r15 := k₇.gpr'
  have r13₇ : s₇.gpr .r13 = s₃.gpr .r13 := ((k₄.trans k₅).trans (k₆.trans k₇)).gpr'
  have r12₇ : s₇.gpr .r12 = s₃.gpr .r12 := ((k₄.trans k₅).trans (k₆.trans k₇)).gpr'
  have x0 := (s₃.gpr .r12).isLt; have x1 := (s₃.gpr .r13).isLt
  have y0 := (s₆.gpr .r14).isLt; have y1 := (s₆.gpr .r15).isLt
  -- the top word
  rw [r14₇, r13₇, r15₇, e₇] at e₈
  have e₈ := e₈ (by omega)
  have u0 := (s₈.gpr .r14).isLt
  have ht : (s₈.gpr .r15).toNat < 2 ^ 63 := by omega
  have f₄ := f₄ ht
  have r12₈ : s₈.gpr .r12 = s₃.gpr .r12 := k₈.gpr'.trans r12₇
  rw [r12₈] at f₁
  rw [f₁, f₂, f₃, f₄] at e₁₀
  have e₁₀ := e₁₀ (by omega)
  have w0 := (s₁₀.gpr .r11).isLt; have w1 := (s₁₀.gpr .rbx).isLt
  have hu : (s₈.gpr .r14).toNat + 2 ^ 64 * (((s₆.gpr .r14).toNat + (s₃.gpr .r13).toNat) / 2 ^ 64) =
      (s₆.gpr .r14).toNat + (s₃.gpr .r13).toNat := by
    clear e₁₀ f₁ f₂ f₃ f₄ e₁ e₃ e₆ e₇
    omega
  have ht' : (s₈.gpr .r15).toNat = (s₆.gpr .r15).toNat + (s₁.gpr .rbp).toNat * (s.gpr .r8).toNat +
      ((s₆.gpr .r14).toNat + (s₃.gpr .r13).toNat) / 2 ^ 64 := by
    clear e₁₀ f₁ f₂ f₃ f₄ e₁ e₃ e₆ e₇
    omega
  rw [ht'] at e₁₀
  obtain ⟨m, hb⟩ := absorb_arith (q := q) (x0 := (s₃.gpr .r12).toNat) (x1 := (s₃.gpr .r13).toNat)
    (y0 := (s₆.gpr .r14).toNat) (y1 := (s₆.gpr .r15).toNat) (u0 := (s₈.gpr .r14).toNat)
    (c1 := ((s₆.gpr .r14).toNat + (s₃.gpr .r13).toNat) / 2 ^ 64)
    a0 a1 a2 hr0 hq e₃ x0 e₆ hu u0 e₁₀ w0 w1
  refine ⟨?_, hb⟩
  rw [hval, m, e₁, hr1]

/-- Absorbing the block at `rsi`. -/
theorem absorb_ok (s : State) {pad : BitVec 32} (hpad : pad = 0 ∨ pad = 1) {q : Nat}
    (hr0 : (s.gpr .r8).toNat < 2 ^ 60) (hr1 : (s.gpr .r9).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s.gpr .r10).toNat = 5 * q)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8) :
    WP isa (.block (absorb pad)) s fun s' =>
      ((s.gpr .rbp).toNat ≤ 4 →
        hval s' % P = ((hval s + (word s.mem (s.gpr .rsi) 0 + 2 ^ 64 * word s.mem (s.gpr .rsi) 8 +
          2 ^ 128 * pad.toNat)) * ((s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r9).toNat)) % P ∧
        (s'.gpr .rbp).toNat ≤ 4) ∧ Keeps absorbRegs s s' :=
  absorbAt_ok s (b := .rsi) (d := 0) (by decide) hpad hr0 hr1 hq hs1 h0 h8

end VG.Proof.Poly1305.X86_64

end

section

/-!
# Poly1305 on x86-64: the final reduction

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

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

end

section

/-!
# Poly1305 on x86-64: the state in memory, and loading the key

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The address `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

theorem contains_off {base : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (off base d) n := by
  simp only [off, ofInt_natCast]; exact Offset.contains_base base h hd

theorem sep_off (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 16)
    (hk : k ≤ 16) (h : d + n ≤ e ∨ e + k ≤ d) : Mem.Sep (off p d) n (off p e) k := by
  simp only [off, ofInt_natCast]; exact Offset.sep p h (by omega) (by omega)

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (sep_off p hd he (by omega) (by omega) h) (by decide)

/-! ## The regions of the state -/

section
variable (st : Addr)
/-- The accumulator. -/
abbrev hR : Region := ⟨st, 24⟩
/-- The key. -/
abbrev kR : Region := ⟨off st 24, 32⟩
/-- The working space: the buffer and the saved registers. -/
abbrev wR : Region := ⟨off st 56, 72⟩
/-- The buffer. -/
abbrev bfR : Region := ⟨off st 56, 16⟩
/-- Where the callee-saved registers are saved. -/
abbrev svR : Region := ⟨off st 72, 48⟩
/-- The whole state. -/
abbrev sR : Region := ⟨st, 128⟩
end

theorem sub_sR (st : Addr) {d n : Nat} (h : d + n ≤ 128) : Region.Sub ⟨off st d, n⟩ (sR st) := by
  intro a ha
  simp only [Region.Contains, off, ofInt_natCast] at *
  bv_omega

theorem kR_disjoint (st : Addr) : ∀ r ∈ [hR st, wR st], (kR st).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> intro a h₁ h₂ <;>
    simp only [Region.Contains, off, ofInt_natCast] at h₁ h₂ <;> bv_omega

/-- The key is unchanged by writes to the accumulator and the working space. -/
theorem key_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') :
    bytesAt m' (off st 24) 32 = bytesAt m (off st 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := kR st) (kR_disjoint st) (by simp) (List.mem_range.mp hi)

theorem hR_contains (st : Addr) {d : Nat} (h : d + 8 ≤ 24) : (hR st).Contains (off st d) 8 := by
  have := contains_off (base := st) (len := 24) h (by omega); simpa using this

theorem wR_contains (st : Addr) {d n : Nat} (h₁ : 56 ≤ d) (h₂ : d + n ≤ 128) :
    (wR st).Contains (off st d) n := by
  simp only [Region.Contains, off, ofInt_natCast]
  rw [show st + BitVec.ofNat 64 d - (st + BitVec.ofNat 64 56) = BitVec.ofNat 64 (d - 56) by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

theorem svR_contains (st : Addr) {d n : Nat} (h₁ : 72 ≤ d) (h₂ : d + n ≤ 120) :
    (svR st).Contains (off st d) n := by
  simp only [Region.Contains, off, ofInt_natCast]
  rw [show st + BitVec.ofNat 64 d - (st + BitVec.ofNat 64 72) = BitVec.ofNat 64 (d - 72) by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

theorem svR_sub_wR (st : Addr) : Region.Sub (svR st) (wR st) := by
  intro a ha
  simp only [Region.Contains, off, ofInt_natCast] at *
  bv_omega

/-! ## The accumulator and the key as numbers -/

theorem off_eq (p : Addr) (d : Nat) : off p d = p + BitVec.ofNat 64 d := by
  simp only [off, ofInt_natCast]

/-- The accumulator stored in the state. -/
theorem leNum_acc (m : Mem) (st : Addr) :
    leNum (bytesAt m st 24) = (m.readW (off st 0) 64).toNat + 2 ^ 64 * (m.readW (off st 8) 64).toNat +
      2 ^ 128 * (m.readW (off st 16) 64).toNat := by
  rw [leNum_bytesAt_24, off_eq, off_eq, off_eq, BitVec.add_zero]
  rfl

/-- The key stored in the state is the 32 bytes at `off st 24`. -/
theorem key_take (m : Mem) (st : Addr) :
    (bytesAt m (off st 24) 32).take 16 = bytesAt m (off st 24) 16 := by
  rw [show 32 = 16 + 16 from rfl, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

theorem key_drop (m : Mem) (st : Addr) :
    ((bytesAt m (off st 24) 32).drop 16).take 16 = bytesAt m (off st 40) 16 := by
  rw [show 32 = 16 + 16 from rfl, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
    List.take_of_length_le (by rw [length_bytesAt])]
  congr 1
  simp only [off, ofInt_natCast]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem leNum_key (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = (m.readW (off p 0) 64).toNat + 2 ^ 64 * (m.readW (off p 8) 64).toNat := by
  rw [leNum_bytesAt_16, off_eq, off_eq, BitVec.add_zero]
  rfl

theorem off_24 (p : Addr) : off p 24 = p + 24 := by rw [off_eq]; rfl

theorem off_off (p : Addr) (d e : Nat) : off (off p d) e = off p (d + e) := by
  simp only [off, ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The clamped `r` as the code computes it. -/
abbrev M0 : BitVec 64 := 0x0ffffffc0fffffff
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

theorem clamp_key (m : Mem) (st : Addr) :
    clamp (leNum ((bytesAt m (off st 24) 32).take 16)) =
      (m.readW (off st 24) 64 &&& M0).toNat + 2 ^ 64 * (m.readW (off st 32) 64 &&& M1).toNat := by
  rw [key_take, leNum_key, off_off, off_off, clamp_words]

theorem r0_lt (k : BitVec 64) : (k &&& M0).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem r1_mod (k : BitVec 64) : (k &&& M1).toNat % 4 = 0 := by
  rw [BitVec.toNat_and, show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_assoc, show M1.toNat &&& 2 ^ 2 - 1 = 0 by decide, Nat.and_zero]

theorem r1_lt (k : BitVec 64) : (k &&& M1).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

end VG.Proof.Poly1305.X86_64

end

/-!
# Poly1305 on x86-64: saving registers, loading the key and the accumulator

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305

open Spec.Poly1305

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let key : Region := ⟨s.gpr .rsi, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key ∧ ret.Disjoint state
  post s s' := Repr s'.mem (s.gpr .rdi) (bytesAt s.mem (s.gpr .rsi) 32) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let blocks : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧ ret.Disjoint state ∧
      (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Repr s.mem (s.gpr .rdi) key msg →
    Repr s'.mem (s.gpr .rdi) key (msg ++ bytesAt s.mem (s.gpr .rsi) (16 * (s.gpr .rdx).toNat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len: usize, …)`:
only `count mod 16`, the number of bytes buffered, matters. The state must be
writable, and it may be permitted to write other regions (which it does
not). -/
def updateX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [data] ∧ state ∈ s.wr ∧ state.Disjoint data ∧ ret.Disjoint state
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .rdi) key msg →
    (s.gpr .rsi).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .rdi) key (msg ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16], …)`:
only `count mod 16`, the number of bytes buffered, matters, and it returns
with `rcx = out`. The state and `out` must be writable, and it may be
permitted to write other regions (which it does not). -/
def finalizeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let out : Region := ⟨s.gpr .rdx, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    state ∈ s.wr ∧ out ∈ s.wr ∧ state.Disjoint out ∧ ret.Disjoint state ∧ ret.Disjoint out
  post s s' := s'.gpr .rcx = s.gpr .rdx ∧ ∀ key msg, Buffered s.mem (s.gpr .rdi) key msg →
    (s.gpr .rsi).toNat % 16 = msg.length % 16 → bytesAt s'.mem (s.gpr .rdx) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

section
variable (s₀ : State)
/-- The state, and the return address, on entry. -/
abbrev st : Addr := s₀.gpr .rdi
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
end

/-- The callee-saved registers of `s` are saved in the state at `st`. -/
def Saved (st : Addr) (s : State) (m : Mem) : Prop :=
  m.readW (off st 72) 64 = s.gpr .rbx ∧ m.readW (off st 80) 64 = s.gpr .rbp ∧
  m.readW (off st 88) 64 = s.gpr .r12 ∧ m.readW (off st 96) 64 = s.gpr .r13 ∧
  m.readW (off st 104) 64 = s.gpr .r14 ∧ m.readW (off st 112) 64 = s.gpr .r15

theorem save_eq : save = [
    .store (at_ .rdi 72) .rbx, .store (at_ .rdi 80) .rbp, .store (at_ .rdi 88) .r12,
    .store (at_ .rdi 96) .r13, .store (at_ .rdi 104) .r14, .store (at_ .rdi 112) .r15] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .rdi 72)), .mov .rbp (.mem (at_ .rdi 80)), .mov .r12 (.mem (at_ .rdi 88)),
    .mov .r13 (.mem (at_ .rdi 96)), .mov .r14 (.mem (at_ .rdi 104)), .mov .r15 (.mem (at_ .rdi 112))] := rfl

set_option simprocs false in
theorem save_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block save) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧
      Frame [svR (s.gpr .rdi)] s.mem s'.mem ∧ Saved (s.gpr .rdi) s s'.mem := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega)⟩
  have o0 := o 72 (by omega); have o1 := o 80 (by omega); have o2 := o 88 (by omega)
  have o3 := o 96 (by omega); have o4 := o 104 (by omega); have o5 := o 112 (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp only [off] at o0 o1 o2 o3 o4 o5
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    State.store64, o0, o1, o2, o3, o4, o5, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
  · have c : ∀ d, 72 ≤ d → d + 8 ≤ 120 → (svR (s.gpr .rdi)).Contains (off (s.gpr .rdi) d) (64 / 8) :=
      fun d h₁ h₂ => svR_contains _ h₁ h₂
    refine (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 72 ?_ ?_)).writeW
      (List.mem_singleton_self _) _ (c 80 ?_ ?_)).writeW (List.mem_singleton_self _) _ (c 88 ?_ ?_)).writeW
      (List.mem_singleton_self _) _ (c 96 ?_ ?_)).writeW (List.mem_singleton_self _) _ (c 104 ?_ ?_)
      |>.writeW (List.mem_singleton_self _) _ (c 112 ?_ ?_) <;> omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) only [off, Mem.readW_writeW_self64, readW_writeW_off]

theorem setup_eq : setup = [
    .movImm64 .rax M0, .mov .r8 (.mem (at_ .rdi 24)), .alu .and .r8 (.reg .rax),
    .movImm64 .rax M1, .mov .r9 (.mem (at_ .rdi 32)), .alu .and .r9 (.reg .rax),
    .mov .r10 (.reg .r9), .shift .shr .r10 2, .alu .add .r10 (.reg .r9),
    .mov .r11 (.mem (at_ .rdi 0)), .mov .rbx (.mem (at_ .rdi 8)), .mov .rbp (.mem (at_ .rdi 16))] := rfl

/-- `s1 = r1 + r1 / 4` is `5 q` for `r1 = 4 q`. -/
theorem s1_toNat (k : BitVec 64) :
    (((k &&& M1) >>> 2) + (k &&& M1)).toNat = 5 * ((k &&& M1).toNat / 4) := by
  have h1 := r1_lt k; have h2 := r1_mod k
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

set_option simprocs false in
theorem setup_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.rd ++ s.wr) :
    WP isa (.block setup) s fun s' =>
      s'.gpr .r8 = s.mem.readW (off (s.gpr .rdi) 24) 64 &&& M0 ∧
      s'.gpr .r9 = s.mem.readW (off (s.gpr .rdi) 32) 64 &&& M1 ∧
      (s'.gpr .r10).toNat = 5 * ((s'.gpr .r9).toNat / 4) ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 0) 64 ∧
      s'.gpr .rbx = s.mem.readW (off (s.gpr .rdi) 8) 64 ∧
      s'.gpr .rbp = s.mem.readW (off (s.gpr .rdi) 16) 64 ∧
      Keeps [.rax, .r8, .r9, .r10, .r11, .rbx, .rbp] s s' := by
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega)⟩
  have i0 := i 0 (by omega); have i8 := i 8 (by omega); have i16 := i 16 (by omega)
  have i24 := i 24 (by omega); have i32 := i 32 (by omega)
  simp only [off] at i0 i8 i16 i24 i32
  apply WP.of_runBlock
  rw [setup_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, execAlu, execShift, arithFlags, State.setReg, State.setFlags, State.load64, i0, i8, i16,
    i24, i32, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, s1_toNat _, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]

end VG.Proof.Poly1305.X86_64

import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Poly1305.X86_64.Arith
import VerifiedGarbage.Impl.Poly1305.X86_64

/-!
# Poly1305 on x86-64: the steps of a block

Untrusted: everything here is checked by Lean. Each lemma runs a few
instructions symbolically and states their effect on the numbers in the
registers.
-/

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
  rw [Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; omega)]
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
/-- `h += m + pad · 2¹²⁸`. -/
theorem addBlock_ok (s : State) {pad : BitVec 32} (hpad : pad = 0 ∨ pad = 1)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8) :
    WP isa (.block (addBlock pad)) s fun s' =>
      ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat +
          (word s.mem (s.gpr .rsi) 0 + 2 ^ 64 * word s.mem (s.gpr .rsi) 8 + 2 ^ 128 * pad.toNat) <
          2 ^ 192 →
        (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
          (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat +
            (word s.mem (s.gpr .rsi) 0 + 2 ^ 64 * word s.mem (s.gpr .rsi) 8 + 2 ^ 128 * pad.toNat)) ∧
      Keeps [.r11, .rbx, .rbp] s s' := by
  have hp : (pad.signExtend 64).toNat = pad.toNat := by rcases hpad with rfl | rfl <;> rfl
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addBlock, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, State.load64, ea_at, h0, h8,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false]
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [word] at hlt ⊢
    rw [add3_toNat _ _ _ _ _ _ (by rw [hp]; omega), hp]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2]

end VG.Proof.Poly1305.X86_64

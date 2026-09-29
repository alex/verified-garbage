import VerifiedGarbage.Proof.Poly1305.X86_64.Steps

/-!
# Poly1305 on x86-64: absorbing a block

Untrusted: everything here is checked by Lean.
-/

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
    [.alu .add .r14 (.reg .r13), .alu .adc .r15 (.reg .rax)] ++
    ([.mov .r11 (.reg .r12), .mov .rbx (.reg .r14), .mov .rbp (.reg .r15),
      .alu .and .rbp (.imm 3), .mov .rax (.reg .r15), .alu .sub .rax (.reg .rbp),
      .shift .shr .r15 2, .alu .add .rax (.reg .r15)] ++
    [.alu .add .r11 (.reg .rax), .alu .adc .rbx (.imm 0), .alu .adc .rbp (.imm 0)]) := rfl

theorem absorbAt_eq (b : Reg) (d : Nat) (pad : BitVec 32) : absorbAt b d pad =
    addBlockAt b d pad ++ (mulTo .r12 .r13 .r11 .r8 ++ (mulAdd .r12 .r13 .rbx .r10 ++
    (mulTo .r14 .r15 .r11 .r9 ++ (mulAdd .r14 .r15 .rbx .r8 ++ (mulAdd .r14 .r15 .rbp .r10 ++
    ([.mov .rax (.reg .rbp), .mul .r8] ++ carry)))))) := by
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

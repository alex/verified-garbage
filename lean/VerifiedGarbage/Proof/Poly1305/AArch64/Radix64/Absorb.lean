import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Steps

namespace VG.Proof.Poly1305.AArch64.Radix64
open VG VG.AArch64 VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.Limbs64 VG.PowLit
open VG.Spec.Poly1305 (P)

abbrev absorbRegs : List Reg := [.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15]

theorem absorb_eq (pad : Bool) : absorb pad =
    addBlock pad ++ (mulTo .x9 .x10 .x4 .x7 ++ (mulAdd .x9 .x10 .x5 .x17 ++
    (mulTo .x11 .x12 .x4 .x8 ++ (mulAdd .x11 .x12 .x5 .x7 ++
    (mulAddSmall .x11 .x12 .x6 .x17 ++ (([.mul .x .x13 .x6 .x7] : List Instr) ++
    (combine ++ (fold ++ addLow)))))))) := by
  simp only [absorb, products, List.append_assoc]

theorem absorb_ok (s : State) (pad : Bool) {q : Nat}
    (hr0 : (s.gpr .x7).toNat < 2 ^ 60) (hr1 : (s.gpr .x8).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s.gpr .x17).toNat = 5 * q)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 8) 8) :
    WP isa (.block (absorb pad)) s fun s' =>
      ((s.gpr .x6).toNat ≤ 4 →
        hval s' % P = ((hval s + (word s.mem (s.gpr .x1) 0 + 2 ^ 64 * word s.mem (s.gpr .x1) 8 +
          2 ^ 128 * pad.toNat)) * ((s.gpr .x7).toNat + 2 ^ 64 * (s.gpr .x8).toNat)) % P ∧
        (s'.gpr .x6).toNat ≤ 4) ∧ Keeps absorbRegs s s' := by
  rw [absorb_eq]
  refine WP.block_append (WP.mono (addBlock_ok s pad h0 h8) fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (mulTo_ok s₁ (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (mulAdd_ok s₂ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₃ ⟨e₃, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (mulTo_ok s₃ (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (mulAdd_ok s₄ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₅ ⟨e₅, k₅⟩ => ?_)
  refine WP.block_append (WP.mono (mulAddSmall_ok s₅) fun s₆ ⟨e₆, k₆⟩ => ?_)
  refine WP.block_append (WP.mono (mulSmall_ok s₆) fun s₇ ⟨e₇, k₇⟩ => ?_)
  refine WP.block_append (WP.mono (combine_ok s₇) fun s₈ ⟨e₈, k₈⟩ => ?_)
  refine WP.block_append (WP.mono (fold_ok s₈) fun s₉ ⟨f₁, f₂, f₃, f₄, k₉⟩ => ?_)
  refine WP.mono (addLow_ok s₉) fun s₁₀ ⟨e₁₀, k₁₀⟩ => ?_
  refine ⟨fun hh2 => ?_, (k₁.trans ((((((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans
    k₈).trans k₉).trans k₁₀)).mono (by decide)⟩
  have hp1 : pad.toNat ≤ 1 := Bool.toNat_le pad
  have hw0 := (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 0) 64).isLt
  have hw8 := (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 8) 64).isLt
  have g0 := (s.gpr .x4).isLt; have g1 := (s.gpr .x5).isLt
  -- h += m
  have e₁ := e₁ (by simp only [word, hval]; omega_using [hh2, hp1, hw0, hw8, g0, g1])
  have a0 := (s₁.gpr .x4).isLt; have a1 := (s₁.gpr .x5).isLt
  have a2 : (s₁.gpr .x6).toNat ≤ 6 := add_arith g0 g1 hh2 hw0 hw8 hp1 e₁ a0 a1
  have r8₁ : s₁.gpr .x7 = s.gpr .x7 := k₁.gpr'
  have r9₁ : s₁.gpr .x8 = s.gpr .x8 := k₁.gpr'
  have r10₁ : s₁.gpr .x17 = s.gpr .x17 := k₁.gpr'
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := absorb_bounds a0 a1 a2 hr0 hq
  -- x = h0 r0
  rw [r8₁] at e₂
  have rbx₂ : s₂.gpr .x5 = s₁.gpr .x5 := k₂.gpr'
  have r10₂ : s₂.gpr .x17 = s.gpr .x17 := k₂.gpr'.trans r10₁
  -- x += h1 s1
  rw [rbx₂, r10₂, hs1] at e₃
  have e₃ := e₃ (by omega_using [e₂, b1, b2])
  rw [e₂] at e₃
  have k₃' := k₂.trans k₃
  have r11₃ : s₃.gpr .x4 = s₁.gpr .x4 := k₃'.gpr'
  have r9₃ : s₃.gpr .x8 = s.gpr .x8 := k₃'.gpr'.trans r9₁
  -- y = h0 r1
  rw [r11₃, r9₃, hr1] at e₄
  have k₄' := k₃'.trans k₄
  have rbx₄ : s₄.gpr .x5 = s₁.gpr .x5 := k₄'.gpr'
  have r8₄ : s₄.gpr .x7 = s.gpr .x7 := k₄'.gpr'.trans r8₁
  -- y += h1 r0
  rw [rbx₄, r8₄] at e₅
  have e₅ := e₅ (by omega_using [e₄, b3, b4])
  rw [e₄] at e₅
  have k₅' := k₄'.trans k₅
  have rbp₅ : s₅.gpr .x6 = s₁.gpr .x6 := k₅'.gpr'
  have r10₅ : s₅.gpr .x17 = s.gpr .x17 := k₅'.gpr'.trans r10₁
  -- y += h2 s1
  rw [rbp₅, r10₅, hs1] at e₆
  have e₆ := e₆ b5 (by omega_using [e₄, b3, b4, b5, e₅])
  rw [e₅] at e₆
  have k₆' := k₅'.trans k₆
  have rbp₆ : s₆.gpr .x6 = s₁.gpr .x6 := k₆'.gpr'
  have r8₆ : s₆.gpr .x7 = s.gpr .x7 := k₆'.gpr'.trans r8₁
  -- h2 r0
  rw [rbp₆, r8₆] at e₇
  have e₇ := e₇ (by omega_using [hr0, b6])
  have r14₇ : s₇.gpr .x11 = s₆.gpr .x11 := k₇.gpr'
  have r15₇ : s₇.gpr .x12 = s₆.gpr .x12 := k₇.gpr'
  have r13₇ : s₇.gpr .x10 = s₃.gpr .x10 := ((k₄.trans k₅).trans (k₆.trans k₇)).gpr'
  have r12₇ : s₇.gpr .x9 = s₃.gpr .x9 := ((k₄.trans k₅).trans (k₆.trans k₇)).gpr'
  have x0 := (s₃.gpr .x9).isLt; have x1 := (s₃.gpr .x10).isLt
  have y0 := (s₆.gpr .x11).isLt; have y1 := (s₆.gpr .x12).isLt
  -- the top word
  rw [r14₇, r13₇, r15₇, e₇] at e₈
  have e₈ := e₈ (by omega_using [hr0, e₂, e₄, b1, b2, b3, b4, b5, b6, e₃, e₅, e₆, e₇])
  have u0 := (s₈.gpr .x11).isLt
  have ht : (s₈.gpr .x12).toNat < 2 ^ 63 := by omega_using [hr0, e₂, e₄, b1, b2, b3, b4, b5, b6, e₃, e₅, e₆, e₇, e₈]
  have f₄ := f₄ ht
  have r12₈ : s₈.gpr .x9 = s₃.gpr .x9 := k₈.gpr'.trans r12₇
  rw [r12₈] at f₁
  dsimp only [hval] at e₁₀
  rw [f₁, f₂, f₃, f₄] at e₁₀
  have e₁₀ := e₁₀ (by omega_using [hr0, e₂, e₄, b1, b2, b3, b4, b5, b6, e₃, e₅, e₆, e₇, e₈])
  have w0 := (s₁₀.gpr .x4).isLt; have w1 := (s₁₀.gpr .x5).isLt
  have hu : (s₈.gpr .x11).toNat + 2 ^ 64 * (((s₆.gpr .x11).toNat + (s₃.gpr .x10).toNat) / 2 ^ 64) =
      (s₆.gpr .x11).toNat + (s₃.gpr .x10).toNat := by
    clear e₁₀ f₁ f₂ f₃ f₄ e₁ e₃ e₆ e₇
    omega_using [e₈]
  have ht' : (s₈.gpr .x12).toNat = (s₆.gpr .x12).toNat + (s₁.gpr .x6).toNat * (s.gpr .x7).toNat +
      ((s₆.gpr .x11).toNat + (s₃.gpr .x10).toNat) / 2 ^ 64 := by
    clear e₁₀ f₁ f₂ f₃ f₄ e₁ e₃ e₆ e₇
    omega_using [e₈, hu]
  rw [ht'] at e₁₀
  obtain ⟨m, hb⟩ := absorb_arith (q := q)
    (w0 := (s₁₀.gpr .x4).toNat) (w1 := (s₁₀.gpr .x5).toNat) (w2 := (s₁₀.gpr .x6).toNat) (x0 := (s₃.gpr .x9).toNat) (x1 := (s₃.gpr .x10).toNat)
    (y0 := (s₆.gpr .x11).toNat) (y1 := (s₆.gpr .x12).toNat) (u0 := (s₈.gpr .x11).toNat)
    (c1 := ((s₆.gpr .x11).toNat + (s₃.gpr .x10).toNat) / 2 ^ 64)
    a0 a1 a2 hr0 hq e₃ x0 e₆ hu u0 (by omega_using [e₁₀]) w0 w1
  refine ⟨?_, hb⟩
  rw [hval, m]
  change (hval s₁ * _) % P = _
  rw [e₁, hr1]

end VG.Proof.Poly1305.AArch64.Radix64

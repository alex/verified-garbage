import VerifiedGarbage.Proof.X25519.AArch64.Ladder

/-!
# X25519 on AArch64: the inversion

`invert` computes `z^(p-2)` left to right over the bits of `p - 2`: at the
counter `n` (from 254 down to 0), `T = z^⌊(p-2) / 2ⁿ⌋`.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519
open Fin.CommRing

/-- The exponent. -/
abbrev ex : Nat := P - 2

/-- The bits of `p - 2 = 2²⁵⁵ - 21` below 254 are set but for bits 2 and 4. -/
theorem ex_bit : ∀ n < 254, ex / 2 ^ n % 2 = if n = 2 ∨ n = 4 then 0 else 1 := by decide +kernel

theorem ex_254 : ex / 2 ^ 254 = 1 := by decide

theorem ex_div (n : Nat) : ex / 2 ^ n = 2 * (ex / 2 ^ (n + 1)) + ex / 2 ^ n % 2 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- The value of `T` at the counter `n`. -/
def tv (z : Fe) (n : Nat) : Fe := z ^ (ex / 2 ^ n)

theorem tv_step (z : Fe) {n : Nat} (hn : n < 254) :
    tv z n = if n = 2 ∨ n = 4 then tv z (n + 1) * tv z (n + 1) else tv z (n + 1) * tv z (n + 1) * z := by
  simp only [tv]
  rw [ex_div n, ex_bit n hn]
  split <;> simp only [Nat.add_zero, pow_add, pow_mul, pow_two, pow_one, mul_pow]

/-- The registers the inversion writes. -/
abbrev invRegs : List Reg := fieldRegs ++ [.x23]

/-- At the counter `n`: `T = z^⌊(p-2) / 2ⁿ⌋`, the other slots as `vals`. -/
def IInv (b : Addr) (s₀ : State) (vals : Nat → Fe) (bnds : Nat → Option Nat) (z : Fe) (n : Nat)
    (s : State) : Prop :=
  Sc b s ∧ Sl s.mem b (Function.update vals 14 (tv z n)) (Function.update bnds 14 (some 18)) ∧
    s.gpr .x23 = BitVec.ofNat 64 n ∧ Kp invRegs s₀ s ∧ Frame [slotArea b] s₀.mem s.mem

theorem sub_eq_zero : ∀ n < 254, ∀ c ∈ [2, 4],
    (BitVec.ofNat 64 n - BitVec.ofNat 64 c == 0) = (n == c) := by decide +kernel

theorem subImm_ok {s : State} {d n : Reg} {c : Nat} (hc : c < 4096) :
    WP isa (.block [.subImm .x d n c]) s fun s' =>
      s'.gpr d = s.gpr n - BitVec.ofNat 64 c ∧ Kp [d] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_subImm_x hc, runStep_some, runBlock_nil, Option.some.injEq,
    exists_eq_left', read_x, gpr_wx_self]
  exact ⟨trivial, kp_wx s _ _, rfl⟩

theorem Inv.of_sl {b : Addr} {s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat} (hs : Sc b s)
    (h : Sl s.mem b vals bnds) : Inv b s s vals bnds := ⟨hs, h, Kp.refl _ _, Frame.refl _ _⟩

/-- One iteration of the inversion, for bit `n`. -/
theorem invBody_ok {b : Addr} {s₀ : State} {vals : Nat → Fe} {bnds : Nat → Option Nat} {z : Fe}
    (hz : vals 2 = z) (hb2 : bnds 2 = some 18) {n : Nat} (hn : n < 254) {s : State}
    (h : IInv b s₀ vals bnds z (n + 1) s) :
    WP isa invBody s fun s' => IInv b s₀ vals bnds z n s' := by
  obtain ⟨hsc, hsl, h23, hkp, hfr⟩ := h
  refine WP.seq (WP.block_append (WP.mono (subImm_ok (d := .x23) (n := .x23) (s := s) (c := 1) (by decide))
    fun s₁ ⟨e₁, k₁, m₁⟩ => ?_))
  have hsc₁ := hsc.of_kp k₁ (by decide)
  have e23 : s₁.gpr .x23 = BitVec.ofNat 64 n := by
    rw [e₁, h23, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), Nat.add_sub_cancel]
  refine WP.mono (mul_inv (Inv.of_sl hsc₁ (by rw [m₁]; exact hsl)) (o := 14) (a := 14) (c := 14)
    (by decide) (by decide) (by decide) (ka := 18) (kc := 18) (by simp) (by simp) (by decide) (by decide))
    fun s₂ h₂ => ?_
  have e23₂ : s₂.gpr .x23 = BitVec.ofNat 64 n := by rw [h₂.kp.gpr _ (by decide), e23]
  have hkp₂ : Kp invRegs s₀ s₂ := ((hkp.trans k₁).trans h₂.kp).sub (List.append_subset.mpr
    ⟨List.append_subset.mpr ⟨List.Subset.refl _, by decide⟩, List.subset_append_left _ _⟩)
  have hfr₂ : Frame [slotArea b] s₀.mem s₂.mem := hfr.trans (by rw [← m₁]; exact h₂.fr)
  simp only [Function.update_self, Function.update_idem] at h₂
  -- the square alone, or times `z`
  have hsq : ((n = 2 ∨ n = 4) ∧ IInv b s₀ vals bnds z n s₂) ∨ (¬(n = 2 ∨ n = 4) ∧
      Inv b s₂ s₂ (Function.update vals 14 (tv z (n + 1) * tv z (n + 1)))
        (Function.update bnds 14 (some 18))) := by
    by_cases hb : n = 2 ∨ n = 4
    · refine .inl ⟨hb, h₂.sc, ?_, e23₂, hkp₂, hfr₂⟩
      rw [tv_step z hn, ite_eq_left hb]
      exact h₂.sl
    · exact .inr ⟨hb, Inv.of_sl h₂.sc h₂.sl⟩
  refine WP.seq (WP.mono (subImm_ok (d := .x17) (n := .x23) (s := s₂) (c := 2) (by decide))
    fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have hsc₃ := h₂.sc.of_kp k₃ (by decide)
  have e23₃ : s₃.gpr .x23 = BitVec.ofNat 64 n := by rw [k₃.gpr _ (by decide), e23₂]
  have hkp₃ : Kp invRegs s₀ s₃ := (hkp₂.trans k₃).sub (List.append_subset.mpr
    ⟨List.Subset.refl _, by decide⟩)
  have hfr₃ : Frame [slotArea b] s₀.mem s₃.mem := by rw [m₃]; exact hfr₂
  refine WP.ite (n == 2) (by simp only [eval, read_x, e₃, e23₂]; rw [sub_eq_zero n hn 2 (by simp)])
    (fun hb => ?_) (fun hb => ?_)
  · have hb' : n = 2 ∨ n = 4 := .inl (by simpa using hb)
    rcases hsq with ⟨-, hq⟩ | ⟨hq, -⟩
    · exact WP.block_nil ⟨hsc₃, by rw [m₃]; exact hq.2.1, e23₃, hkp₃, hfr₃⟩
    · exact absurd hb' hq
  refine WP.seq (WP.mono (subImm_ok (d := .x17) (n := .x23) (s := s₃) (c := 4) (by decide))
    fun s₄ ⟨e₄, k₄, m₄⟩ => ?_)
  have hsc₄ := hsc₃.of_kp k₄ (by decide)
  have e23₄ : s₄.gpr .x23 = BitVec.ofNat 64 n := by rw [k₄.gpr _ (by decide), e23₃]
  have hkp₄ : Kp invRegs s₀ s₄ := (hkp₃.trans k₄).sub (List.append_subset.mpr
    ⟨List.Subset.refl _, by decide⟩)
  have hfr₄ : Frame [slotArea b] s₀.mem s₄.mem := by rw [m₄]; exact hfr₃
  refine WP.ite (n == 4) (by simp only [eval, read_x, e₄, e23₃]; rw [sub_eq_zero n hn 4 (by simp)])
    (fun hb4 => ?_) (fun hb4 => ?_)
  · have hb' : n = 2 ∨ n = 4 := .inr (by simpa using hb4)
    rcases hsq with ⟨-, hq⟩ | ⟨hq, -⟩
    · exact WP.block_nil ⟨hsc₄, by rw [m₄, m₃]; exact hq.2.1, e23₄, hkp₄, hfr₄⟩
    · exact absurd hb' hq
  · have hb' : ¬(n = 2 ∨ n = 4) := by simp only [beq_eq_false_iff_ne] at hb hb4; omega
    rcases hsq with ⟨hq, -⟩ | ⟨-, hq⟩
    · exact absurd hq hb'
    · have hI : Inv b s₄ s₄ (Function.update vals 14 (tv z (n + 1) * tv z (n + 1)))
          (Function.update bnds 14 (some 18)) := Inv.of_sl hsc₄ (by rw [m₄, m₃]; exact hq.sl)
      refine WP.mono (mul_inv hI (o := 14) (a := 14) (c := 2) (by decide) (by decide) (by decide)
        (ka := 18) (kc := 18) (by simp) (by simp [hb2]) (by decide) (by decide)) fun s₅ h₅ => ?_
      refine ⟨h₅.sc, ?_, by rw [h₅.kp.gpr _ (by decide), e23₄], (hkp₄.trans h₅.kp).sub
        (List.append_subset.mpr ⟨List.Subset.refl _, List.subset_append_left _ _⟩), hfr₄.trans h₅.fr⟩
      simp only [Function.update_self, Function.update_idem, Function.update_of_ne (show (2 : Nat) ≠ 14 by decide),
        hz] at h₅
      rw [tv_step z hn, ite_eq_right hb']
      exact h₅.sl

theorem tv_254 (z : Fe) : tv z 254 = z := by simp only [tv, ex_254, pow_one]

theorem tv_0 (z : Fe) : tv z 0 = pow z (P - 2) := by simp only [tv, pow_eq, Nat.pow_zero, Nat.div_one]

/-- `[T] = [Z2]^(p-2)`. -/
theorem invert_ok {b : Addr} {s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat} {z : Fe}
    (hsc : Sc b s) (hsl : Sl s.mem b vals bnds) (hz : vals 2 = z) (hb2 : bnds 2 = some 18) :
    WP isa Impl.X25519.AArch64.invert s fun s' => Sc b s' ∧
      Sl s'.mem b (Function.update vals 14 (pow z (P - 2))) (Function.update bnds 14 (some 18)) ∧
      Kp invRegs s s' ∧ Frame [slotArea b] s.mem s'.mem := by
  refine WP.seq (WP.block_append (WP.mono (copy_inv (Inv.of_sl hsc hsl) (o := 14) (a := 2) (by decide)
    (by decide) hb2) fun s₁ h₁ => ?_))
  refine WP.block_cons_iff.mpr ⟨_, exec_movz, WP.block_nil ?_⟩
  refine WP.loop (M := isa) (fun n s₂ => 1 ≤ n ∧ n ≤ 254 ∧ IInv b s vals bnds z n s₂)
    (fun n s₂ ⟨h1, h254, hI⟩ => ?_) 254 _ ⟨by decide, by decide, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (invBody_ok hz hb2 (by omega) hI) fun s₃ h₃ => ?_
    have hev : isa.eval (.nonzero .x .x23) s₃ = some (BitVec.ofNat 64 m != 0) := by
      simp only [eval, read_x, h₃.2.2.1]
    by_cases hm : m = 0
    · subst hm
      refine .inl ⟨by rw [hev]; rfl, h₃.1, ?_, h₃.2.2.2⟩
      rw [← tv_0]; exact h₃.2.1
    · refine .inr ⟨?_, m, by omega, by omega, by omega, h₃⟩
      rw [hev]
      have : BitVec.ofNat 64 m ≠ 0 := fun h => hm (by
        have := congrArg BitVec.toNat h
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this)
      simpa using this
  · refine ⟨sc_wx _ _ h₁.sc (by decide), ?_, gpr_wx_self _ _ _, (h₁.kp.trans (kp_wx _ _ _)).sub
      (List.append_subset.mpr ⟨List.subset_append_left _ _, by decide⟩), h₁.fr⟩
    rw [mem_wx, tv_254, ← hz]
    simpa only [Function.update_idem] using h₁.sl

end VG.Proof.X25519.AArch64

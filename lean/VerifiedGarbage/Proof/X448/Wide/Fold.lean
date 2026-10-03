import VerifiedGarbage.Proof.X448.Wide.Pass
import VerifiedGarbage.Proof.X448.AArch64.Carry

/-! Untrusted: fold a carry into wide limbs 0 and 4. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem coeff_limbs (m : Mem) (base : Addr) (o i : Nat) :
    coeff m base o i = limbs m base o (2 * i) + 2 ^ 64 * limbs m base o (2 * i + 1) := by
  have e0 : o + 8 * (2 * i) = o + 16 * i := by omega
  have e1 : o + 8 * (2 * i + 1) = o + 16 * i + 8 := by omega
  simp only [coeff, pair, limbs, e0, e1]

theorem foldLimb_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 8)
    (hb : coeff s.mem base TMP k + (s.gpr .x6).toNat < 2 ^ 64) :
    WP isa (.block [ld .x4 (TMP + 16 * k), .add .x .x4 .x4 .x6, st .x4 (TMP + 16 * k)]) s fun t =>
      (∀ i < 8, coeff t.mem base TMP i =
        if i = k then coeff s.mem base TMP i + (s.gpr .x6).toNat else coeff s.mem base TMP i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps [.x4] s t := by
  have e : TMP + 8 * (2 * k) = TMP + 16 * k := by omega
  have low : limbs s.mem base TMP (2 * k) + (s.gpr .x6).toNat < 2 ^ 64 := by
    rw [coeff_limbs] at hb
    omega
  have run := VG.Proof.X448.AArch64.foldLimb_ok hs (k := 2 * k) (by omega) low
  rw [e] at run
  refine WP.mono run fun t ⟨tf, tm, tk⟩ => ⟨?_, tm, tk⟩
  intro i hi
  rw [coeff_limbs, tf (2 * i) (by omega), tf (2 * i + 1) (by omega),
    ite_eq_right (by omega : 2 * i + 1 ≠ 2 * k), coeff_limbs]
  by_cases h : i = k
  · subst i
    rw [ite_eq_left rfl, ite_eq_left rfl]
    omega
  · rw [ite_eq_right (by omega : 2 * i ≠ 2 * k), ite_eq_right h]

theorem fold_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 8, coeff s.mem base TMP i = digit f i)
    (hc : (s.gpr .x6).toNat = carry f 8) (hb : carry f 8 < 2 ^ 63) :
    WP isa (.block fold) s fun t =>
      (∀ i < 8, coeff t.mem base TMP i = folded f i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps [.x4] s t := by
  have bound : ∀ i < 8, digit f i + carry f 8 < 2 ^ 64 := by
    intro i _
    have h := digit_lt f i
    simp only [radix] at h
    omega
  change WP isa (.block
    (([ld .x4 (TMP + 16 * 0), .add .x .x4 .x4 .x6,
       st .x4 (TMP + 16 * 0)] : List Instr) ++
     [ld .x4 (TMP + 16 * 4), .add .x .x4 .x4 .x6,
       st .x4 (TMP + 16 * 4)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (foldLimb_ok hs (k := 0) (by decide)
    (by rw [hf 0 (by decide), hc]; exact bound 0 (by decide))) fun u ⟨uf, um, uk⟩ => ?_
  have uc : (u.gpr .x6).toNat = carry f 8 := by rw [uk.1 _ (by decide), hc]
  refine WP.mono (foldLimb_ok (hs.of_keeps uk (by decide)) (k := 4) (by decide) ?_)
    fun t ⟨tf, tm, tk⟩ => ?_
  · rw [uf 4 (by decide), ite_eq_right (by decide), hf 4 (by decide), uc]
    exact bound 4 (by decide)
  · refine ⟨?_, um.trans tm, uk.trans tk⟩
    intro i hi
    rw [tf i hi, uf i hi, hf i hi, hc, uc]
    simp only [folded]
    by_cases h0 : i = 0
    · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
    · by_cases h4 : i = 4
      · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
      · simp only [h0, h4, ite_false, false_or, Nat.add_zero]

end VG.Proof.X448.Wide

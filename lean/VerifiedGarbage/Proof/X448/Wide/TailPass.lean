import VerifiedGarbage.Proof.X448.Wide.PassInit
import VerifiedGarbage.Proof.X448.Wide.TailStep

/-! Untrusted: in-place or disjoint wide carry propagation. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem tailPass_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0)
    (hsep : o = TMP ∨ o + 128 ≤ TMP ∨ TMP + 128 ≤ o) (unpack : Bool)
    (hfalse : unpack = false → o = TMP)
    {f : Nat → Nat} (hf : ∀ i < 8, coeff s.mem base TMP i = f i)
    (hb : ∀ i < 8, f i < 2 ^ 63 + radix) :
    WP isa (.block (Impl.X448.AArch64.Tail.pass o unpack)) s fun t =>
      (∀ i < 8, coeff t.mem base o i = encoded (digit f i) unpack) ∧
      (t.gpr .x6).toNat = carry f 8 ∧ Outside base o 128 s.mem t.mem ∧ Keeps colRegs s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, coeff t.mem base o i = encoded (digit f i) unpack) ∧
    (∀ i, k ≤ i → i < 8 → coeff t.mem base TMP i = f i) ∧
    (t.gpr .x6).toNat = carry f k ∧ t.gpr .x11 = 0 ∧
    t.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps colRegs s t
  have step : ∀ k t, k < 8 → inv k t → WP isa (.block (Impl.X448.AArch64.Tail.step o k unpack)) t (inv (k + 1)) := by
    intro k t hk ⟨tl, th, tc, tz, t9, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    have te := th k (by omega) hk
    have cap : coeff t.mem base TMP k + (t.gpr .x6).toNat < 2 ^ 64 := by
      rw [te, tc]
      have c := carry_small (n := k) (fun i hi => hb i (by omega))
      have h := hb k hk
      simp only [radix] at h
      omega
    refine WP.mono (tailStep_ok ts ho ho8 hk unpack hfalse t9 cap) fun u ⟨uc, uv, um, uk⟩ => ?_
    rw [te, tc] at uc uv
    refine ⟨?_, ?_, uc, (uk.1 _ (by decide)).trans tz, (uk.1 _ (by decide)).trans t9,
      tm.trans (um.mono (by omega) (by omega)), tk.trans (uk.mono (by decide))⟩
    · intro i hi
      by_cases h : i = k
      · subst i
        exact uv
      · have eq : coeff u.mem base o i = coeff t.mem base o i :=
          outside_coeff um (by omega) (by omega)
        rw [eq]
        exact tl i (by omega)
    · intro i hi hi'
      have sep : TMP + 16 * i + 16 ≤ o + 16 * k ∨ o + 16 * k + 16 ≤ TMP + 16 * i := by
        rcases hsep with h | h | h <;> omega
      have eq : coeff u.mem base TMP i = coeff t.mem base TMP i :=
        outside_coeff um sep (by simp only [TMP]; omega)
      rw [eq]
      exact th i (by omega) hi'
  rw [Impl.X448.AArch64.Tail.pass, WP.block_append_iff]
  refine WP.mono (passInit_ok s) fun u ⟨u6, uz, u9, um, uk⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) u ?_)
    fun t ⟨tl, _, tc, _, _, tm, tk⟩ => ⟨tl, tc, tm, tk⟩
  refine ⟨fun _ hi => by omega, ?_, ?_, uz, u9, ?_, uk⟩
  · intro i _ hi; rw [um]; exact hf i hi
  · rw [u6]; rfl
  · rw [um]; exact Outside.refl _ _ _ _

end VG.Proof.X448.Wide

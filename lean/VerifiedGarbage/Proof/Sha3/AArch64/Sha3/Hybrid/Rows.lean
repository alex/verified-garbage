import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Cache

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid
open VG.Proof.Sha3 (B out outState)

def Progress (r : Nat) (A : Spec.Sha3.State) (rc : BitVec 64) (n : Nat) (s : VG.AArch64.State) : Prop :=
  ∀ i < 25, value s (laneSlot (loc (r + 1) i)) =
    if i < n then out A rc (i % 5) (i / 5) else B A (i % 5) (i / 5)

def RowInv (s₀ : VG.AArch64.State) (r : Nat) (A : Spec.Sha3.State) (n : Nat)
    (s : VG.AArch64.State) : Prop :=
  Keep s₀ s ∧ Progress r A (s₀.gpr .x16) n s

theorem row_ok (r y : Nat) (hr : r < 24) (hy : y < 5) (s₀ : VG.AArch64.State) (A : Spec.Sha3.State)
    (hp : Progress r A (s₀.gpr .x16) (5 * y) s₀) :
    WP isa (.block (row r y)) s₀ (RowInv s₀ r A (5 * (y + 1))) := by
  unfold row
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (save_pair_ok r y hy s₀).mono fun ss ⟨hks, hls, hvs⟩ => ?_
  refine (cacheRow_ok r y hr hy ss).mono fun s₁ ⟨hkc, hlc, hvc, hcache⟩ => ?_
  have hk := hks.trans hkc
  have hl : ∀ i < 25, value s₁ (laneSlot i) = value s₀ (laneSlot i) :=
    fun i hi => (hlc i).trans (hls i hi)
  have hv : ∀ j < 2, value s₁ (savedSlot (rowSlot r j y) j) = value s₀ (rowSlot r j y) :=
    fun j hj => (hvc j).trans (hvs j hj)
  let inv := fun x s => RowInv s₀ r A (5 * y + x) s ∧
    (∀ j < 2, value s (savedSlot (rowSlot r j y) j) = B A j y) ∧
    (cacheSource r y ≠ none → ∀ j < 5, isGpr (rowSlot r j y) = true → value s (.v .v30) = B A j y)
  have hstart : inv 0 s₁ := by
    refine ⟨⟨hk, fun i hi => ?_⟩, (fun j hj => ?_), fun hn j hj hg => ?_⟩
    · rw [hl _ (loc_bound _ _ hi)]
      exact hp i hi
    · rw [hv j hj]
      have h := hp (j + 5 * y) (by omega)
      simp only [show ¬j + 5 * y < 5 * y by omega, ite_false,
        show (j + 5 * y) % 5 = j by omega, show (j + 5 * y) / 5 = y by omega] at h
      exact h
    · rw [hcache hn j hj hg]
      change value ss (laneSlot (loc (r + 1) (j + 5 * y))) = _
      rw [hls _ (loc_bound _ _ (by omega))]
      have h := hp (j + 5 * y) (by omega)
      simpa only [show ¬j + 5 * y < 5 * y by omega, ite_false,
        show (j + 5 * y) % 5 = j by omega, show (j + 5 * y) / 5 = y by omega] using h
  have hloop : WP isa (.block ((List.range 5).flatMap fun x => chi r x y)) s₁ (inv 5) := by
    refine wp_range_flatMap (M := isa) inv (fun x s hx ⟨⟨hs, hpr⟩, hb, hcv⟩ => ?_)
      5 (Nat.le_refl _) s₁ hstart
    have hi : ∀ j < 5, j = x ∨ j = (x + 1) % 5 ∨ j = (x + 2) % 5 →
        value s (chiSlot r j y) = B A j y := by
      intro j hj hchoice
      dsimp only [chiSlot]
      split
      · rename_i h
        exact hcv h.1 j hj (by rw [← base_isGpr]; exact h.2)
      · unfold chiBaseSlot
        split
        · exact hb j (by assumption)
        · have hn : x ≤ j := by omega
          have h := hpr (j + 5 * y) (by omega)
          simp only [show ¬j + 5 * y < 5 * y + x by omega, ite_false,
            show (j + 5 * y) % 5 = j by omega, show (j + 5 * y) / 5 = y by omega] at h
          exact h
    refine (chi_ok r x y hr hx hy s A hi).mono fun s' ⟨hh, hcv', hb', hl'⟩ => ?_
    refine ⟨⟨hs.trans hh, fun i hi => ?_⟩, (fun j hj => (hb' j hj).trans (hb j hj)),
      fun hn j hj hg => (hcv' hn).trans (hcv hn j hj hg)⟩
    rw [hl' i hi]
    by_cases he : i = x + 5 * y
    · subst i
      simp only [ite_true, hs.x16, show x + 5 * y < 5 * y + (x + 1) by omega,
        show (x + 5 * y) % 5 = x by omega, show (x + 5 * y) / 5 = y by omega]
    · have hn : (i < 5 * y + (x + 1)) ↔ (i < 5 * y + x) := by omega
      simp only [he, ite_false, hpr i hi, hn]
  exact hloop.mono fun s' h => by
    have he : 5 * y + 5 = 5 * (y + 1) := by omega
    rw [← he]
    exact h.1

theorem rows_ok (r : Nat) (hr : r < 24) (s₀ : VG.AArch64.State) (A : Spec.Sha3.State)
    (hb : ∀ x < 5, ∀ y < 5, value s₀ (rowSlot r x y) = B A x y) :
    WP isa (.block ((List.range 5).flatMap (row r))) s₀ fun s' =>
      Keep s₀ s' ∧ Lanes s' (r + 1) (outState A (s₀.gpr .x16)) := by
  have hp : Progress r A (s₀.gpr .x16) 0 s₀ := by
    intro i hi
    rw [ite_eq_right (by omega)]
    have h := hb (i % 5) (by omega) (i / 5) (by omega)
    simpa only [rowSlot, show i % 5 + 5 * (i / 5) = i by omega] using h
  have hh : WP isa (.block ((List.range 5).flatMap (row r))) s₀ (RowInv s₀ r A 25) := by
    refine wp_range_flatMap (M := isa) (fun y => RowInv s₀ r A (5 * y))
      (fun y s hy ⟨hs, hp'⟩ => ?_) 5 (Nat.le_refl _) s₀ ⟨Keep.refl _, hp⟩
    have hlocal : Progress r A (s.gpr .x16) (5 * y) s := by rw [hs.x16]; exact hp'
    exact (row_ok r y hr hy s A hlocal).mono fun s' ⟨hk, hp''⟩ =>
      ⟨hs.trans hk, by rwa [hs.x16] at hp''⟩
  refine hh.mono fun s' ⟨hk, hp'⟩ => ⟨hk, fun i hi => ?_⟩
  rw [hp' i hi, ite_eq_left hi]
  simp only [outState, Vector.getElem_ofFn]

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

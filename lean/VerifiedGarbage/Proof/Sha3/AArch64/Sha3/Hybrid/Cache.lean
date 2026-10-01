import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Save

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid

theorem saved_ne_v30 (a : Slot) (i : Nat) : savedSlot a i ≠ .v .v30 := by
  cases a <;> simp only [savedSlot]
  all_goals split <;> decide

theorem base_isGpr (r x y : Nat) : isGpr (chiBaseSlot r x y) = isGpr (rowSlot r x y) := by
  unfold chiBaseSlot
  split
  · cases rowSlot r x y <;> rfl
  · rfl

theorem cache_source (r y : Nat) (hr : r < 24) (hy : y < 5) (g : VG.AArch64.Reg)
    (he : cacheSource r y = some g) (j : Nat) (hj : j < 5) (hg : isGpr (rowSlot r j y) = true) :
    rowSlot r j y = .g g := by
  have h : ∀ r < 24, ∀ y < 5, ∀ j < 5,
      (cacheSource r y).isSome = true → isGpr (rowSlot r j y) = true →
        rowSlot r j y = .g ((cacheSource r y).getD .x0) := by decide
  have hh := h r hr y hy j hj
  simpa only [he, Option.isSome_some, Option.getD_some] using hh (by simp only [he, Option.isSome_some]) hg

theorem cacheRow_ok (r y : Nat) (hr : r < 24) (hy : y < 5) (s : VG.AArch64.State) :
    WP isa (.block (cacheRow r y)) s fun s' =>
      Keep s s' ∧ (∀ i, value s' (laneSlot i) = value s (laneSlot i)) ∧
      (∀ j, value s' (savedSlot (rowSlot r j y) j) = value s (savedSlot (rowSlot r j y) j)) ∧
      (cacheSource r y ≠ none → ∀ j < 5, isGpr (rowSlot r j y) = true →
        value s' (.v .v30) = value s (rowSlot r j y)) := by
  unfold cacheRow
  cases he : cacheSource r y with
  | none =>
    apply WP.block_nil
    exact ⟨Keep.refl _, fun _ => rfl, fun _ => rfl, fun h => False.elim (h rfl)⟩
  | some g =>
    refine WP.cons rfl (wp_nil ?_)
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun i => ?_, fun j => ?_, fun _ j hj hg => ?_⟩
    · rw [value_setV, ite_eq_right (slot_ne_v i _ vother_temps.2.2.1)]
    · rw [value_setV, ite_eq_right (saved_ne_v30 _ _)]
    · rw [cache_source r y hr hy g he j hj hg]
      simp only [value, RegUpd.v_setV_self, vdword_ofVDwords_0]

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

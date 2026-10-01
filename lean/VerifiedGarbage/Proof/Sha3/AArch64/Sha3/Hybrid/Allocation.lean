import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.ChiCore

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid

def allGpr (r x y : Nat) : Bool :=
  isGpr (chiSlot r x y) && isGpr (chiSlot r ((x + 1) % 5) y) && isGpr (chiSlot r ((x + 2) % 5) y)

def destination (r x y : Nat) : VReg := match rowSlot r x y with | .v v => v | .g _ => .v31

theorem prep_safe : ∀ r < 24, ∀ x < 5, ∀ y < 5,
    PrepSafe (chiSlot r x y) (chiSlot r ((x + 1) % 5) y) (chiSlot r ((x + 2) % 5) y)
      (chiTemp (allGpr r x y) 0) (chiTemp (allGpr r x y) 1) (chiTemp (allGpr r x y) 2) := by
  decide

theorem chiTemp_other (b : Bool) (i : Nat) (hi : i < 3) : VOther (chiTemp b i) := by
  have h : ∀ b : Bool, ∀ i < 3, ∀ j < 20, vreg j ≠ chiTemp b i := by decide
  exact h b i hi

theorem destination_other (r x y : Nat) :
    decide (x = 0 ∧ y = 0) = true → destination r x y ≠ .v31 := by
  intro h
  have h0 : x = 0 ∧ y = 0 := of_decide_eq_true h
  rcases h0 with ⟨rfl, rfl⟩
  have hz : VG.Impl.Sha3.AArch64.Sha3.Hybrid.loc (r + 1) 0 = 0 := by
    have h : ∀ r, VG.Impl.Sha3.AArch64.Sha3.Hybrid.loc r 0 = 0 := by
      intro r; induction r with
      | zero => rfl
      | succ r ih => exact ih
    exact h _
  simp only [destination, rowSlot, Nat.mul_zero, Nat.zero_add, hz, laneSlot,
    show 0 < 20 by decide, ite_true]
  decide

theorem core_other_state (r x y i : Nat) (h : laneSlot i ≠ rowSlot r x y) :
    CoreOther (chiSlot r x y) (chiSlot r ((x + 1) % 5) y) (chiSlot r ((x + 2) % 5) y)
      (chiTemp (allGpr r x y) 0) (chiTemp (allGpr r x y) 1)
      (chiTemp (allGpr r x y) 2) (destination r x y) (decide (x = 0 ∧ y = 0)) (laneSlot i) := by
  refine ⟨fun _ => slot_ne_v i _ (chiTemp_other _ _ (by decide)),
    fun _ => slot_ne_v i _ (chiTemp_other _ _ (by decide)),
    fun _ => slot_ne_v i _ (chiTemp_other _ _ (by decide)), ?_,
    fun _ => slot_ne_v i _ vother_temps.2.2.2⟩
  unfold destination
  split
  · rename_i v he
    rw [he] at h
    exact h
  · exact slot_ne_v i _ vother_temps.2.2.2

theorem saved_ne_state (a : Slot) (j i : Nat) (_hj : j < 2) (hi : i < 25) :
    savedSlot a j ≠ laneSlot i := by
  cases a <;> simp only [savedSlot]
  all_goals split
  · exact (slot_ne_v i _ vother_temps.1).symm
  · exact (slot_ne_v i _ vother_temps.2.1).symm
  · exact (slot_ne_g i hi _ gother_temps.1).symm
  · exact (slot_ne_g i hi _ gother_temps.2.1).symm

theorem saved_core_other (r x y j : Nat) (hr : r < 24) (hx : x < 5) (hy : y < 5) (hj : j < 2) :
    CoreOther (chiSlot r x y) (chiSlot r ((x + 1) % 5) y) (chiSlot r ((x + 2) % 5) y)
      (chiTemp (allGpr r x y) 0) (chiTemp (allGpr r x y) 1)
      (chiTemp (allGpr r x y) 2) (destination r x y) (decide (x = 0 ∧ y = 0))
      (savedSlot (rowSlot r j y) j) := by
  have h : ∀ r < 24, ∀ x < 5, ∀ y < 5, ∀ j < 2,
      CoreOther (chiSlot r x y) (chiSlot r ((x + 1) % 5) y) (chiSlot r ((x + 2) % 5) y)
        (chiTemp (allGpr r x y) 0) (chiTemp (allGpr r x y) 1)
        (chiTemp (allGpr r x y) 2) (destination r x y) (decide (x = 0 ∧ y = 0))
        (savedSlot (rowSlot r j y) j) := by decide
  exact h r hr x hx y hy j hj

theorem cached_core_other : ∀ r < 24, ∀ x < 5, ∀ y < 5, cacheSource r y ≠ none →
    CoreOther (chiSlot r x y) (chiSlot r ((x + 1) % 5) y) (chiSlot r ((x + 2) % 5) y)
      (chiTemp (allGpr r x y) 0) (chiTemp (allGpr r x y) 1)
      (chiTemp (allGpr r x y) 2) (destination r x y) (decide (x = 0 ∧ y = 0)) (.v .v30) := by decide

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

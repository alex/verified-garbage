import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Allocation
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.IntegerChi

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid
open VG.Proof.Sha3 (B out)

theorem rowSlot_inj (r x y i : Nat) (hx : x < 5) (hy : y < 5) (hi : i < 25) :
    laneSlot (loc (r + 1) i) = rowSlot r x y ↔ i = x + 5 * y := by
  have hn : x + 5 * y < 25 := by omega
  exact ⟨fun h => loc_inj _ _ _ hi hn
    (slot_inj _ (loc_bound _ _ hi) _ (loc_bound _ _ hn) h),
    fun h => congrArg (fun j => laneSlot (loc (r + 1) j)) h⟩

theorem chiVector_ok (r x y : Nat) (hr : r < 24) (hx : x < 5) (hy : y < 5)
    (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (hb : ∀ j < 5, j = x ∨ j = (x + 1) % 5 ∨ j = (x + 2) % 5 →
      value s (chiSlot r j y) = B A j y) :
    WP isa (.block (chiVector r x y)) s fun s' =>
      Keep s s' ∧
      (cacheSource r y ≠ none → value s' (.v .v30) = value s (.v .v30)) ∧
      (∀ j < 2, value s' (savedSlot (rowSlot r j y) j) = value s (savedSlot (rowSlot r j y) j)) ∧
      ∀ i < 25, value s' (laneSlot (loc (r + 1) i)) = if i = x + 5 * y
        then out A (s.gpr .x16) x y else value s (laneSlot (loc (r + 1) i)) := by
  have hword : chiWord (value s (chiSlot r x y)) (value s (chiSlot r ((x + 1) % 5) y))
      (value s (chiSlot r ((x + 2) % 5) y)) (s.gpr .x16) (decide (x = 0 ∧ y = 0)) =
      out A (s.gpr .x16) x y := by
    simp (disch := omega) only [hb, chiWord, out, decide_eq_true_eq]
  unfold chiVector
  change WP isa (.block (chiCore (chiSlot r x y) (chiSlot r ((x + 1) % 5) y)
    (chiSlot r ((x + 2) % 5) y) (chiTemp (allGpr r x y) 0)
    (chiTemp (allGpr r x y) 1) (chiTemp (allGpr r x y) 2) (destination r x y)
    (decide (x = 0 ∧ y = 0)) ++
    (match rowSlot r x y with | .v _ => [] | .g g => [.umov .x g .v31 0]))) s _
  rw [WP.block_append_iff]
  refine (chiCore_ok s _ _ _ _ _ _ _ _ (prep_safe r hr x hx y hy) (destination_other r x y)).mono
    fun s₁ ⟨hout, hk, _, ho⟩ => ?_
  rw [hword] at hout
  have hcache : cacheSource r y ≠ none → value s₁ (.v .v30) = value s (.v .v30) :=
    fun h => ho _ (cached_core_other r hr x hx y hy h)
  have hphys : ∀ i < 25, i ≠ x + 5 * y →
      value s₁ (laneSlot (loc (r + 1) i)) = value s (laneSlot (loc (r + 1) i)) := by
    intro i hi he
    exact ho _ (core_other_state r x y _ (fun h => he ((rowSlot_inj r x y i hx hy hi).mp h)))
  have hsaved : ∀ j < 2, value s₁ (savedSlot (rowSlot r j y) j) =
      value s (savedSlot (rowSlot r j y) j) := fun j hj => ho _ (saved_core_other r x y j hr hx hy hj)
  have hstate : ∀ j < 2, savedSlot (rowSlot r j y) j ≠ rowSlot r x y :=
    fun j hj => saved_ne_state _ j _ hj (loc_bound _ _ (by omega))
  cases he : rowSlot r x y with
  | v v =>
    have hd : destination r x y = v := by simp only [destination, he]
    apply WP.block_nil
    refine ⟨hk, hcache, hsaved, fun i hi => ?_⟩
    by_cases h : i = x + 5 * y
    · subst i
      rw [ite_eq_left rfl]
      change value s₁ (rowSlot r x y) = _
      rw [he]
      rw [hd] at hout
      exact hout
    · simp only [h, ite_false, hphys i hi h]
  | g g =>
    have hd : destination r x y = .v31 := by simp only [destination, he]
    have hg0 : g ≠ .x0 := by
      have h : GOther .x0 := by unfold GOther; decide
      intro e; subst g
      exact slot_ne_g _ (loc_bound _ _ (by omega)) _ h he
    have hg16 : g ≠ .x16 := by
      intro e; subst g
      exact slot_ne_g _ (loc_bound _ _ (by omega)) _ gother_temps.2.2.1 he
    apply WP.of_runBlock
    rw [runBlock_cons, exec_umov_low, runStep_some, runBlock_nil]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · exact hk.trans ⟨by simp only [RegUpd.gpr_write, Ne.symm hg0, ite_false],
        by simp only [RegUpd.gpr_write, Ne.symm hg16, ite_false], rfl, rfl, rfl, rfl⟩
    · exact hcache
    · intro j hj
      rw [value_write, ite_eq_right (by rw [← he]; exact hstate j hj), hsaved j hj]
    · intro i hi
      rw [value_write]
      have hj : laneSlot (loc (r + 1) i) = .g g ↔ i = x + 5 * y := by
        rw [← he]; exact rowSlot_inj r x y i hx hy hi
      simp only [hj]
      by_cases h : i = x + 5 * y
      · simp only [h, ite_true]
        rw [hd] at hout
        exact hout
      · simp only [h, ite_false, hphys i hi h]

theorem chi_input_ne_x17 : ∀ r < 24, ∀ x < 5, ∀ y < 5, chiSlot r x y ≠ .g .x17 := by decide

theorem saved_ne_x17 (a : Slot) (j : Nat) : savedSlot a j ≠ .g .x17 := by
  cases a <;> simp only [savedSlot]
  all_goals split <;> decide

theorem chi_ok (r x y : Nat) (hr : r < 24) (hx : x < 5) (hy : y < 5)
    (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (hb : ∀ j < 5, j = x ∨ j = (x + 1) % 5 ∨ j = (x + 2) % 5 →
      value s (chiSlot r j y) = B A j y) :
    WP isa (.block (chi r x y)) s fun s' =>
      Keep s s' ∧
      (cacheSource r y ≠ none → value s' (.v .v30) = value s (.v .v30)) ∧
      (∀ j < 2, value s' (savedSlot (rowSlot r j y) j) = value s (savedSlot (rowSlot r j y) j)) ∧
      ∀ i < 25, value s' (laneSlot (loc (r + 1) i)) = if i = x + 5 * y
        then out A (s.gpr .x16) x y else value s (laneSlot (loc (r + 1) i)) := by
  have hvec := chiVector_ok r x y hr hx hy s A hb
  unfold chi
  split
  next a b c dest ha hb' hc hd =>
    have ha17 : a ≠ .x17 := fun he => chi_input_ne_x17 r hr x hx y hy (ha.trans (congrArg Slot.g he))
    have hc17 : c ≠ .x17 := fun he => chi_input_ne_x17 r hr _ (by omega) y hy (hc.trans (congrArg Slot.g he))
    have hd0 : dest ≠ .x0 := by
      intro he
      have ho : GOther .x0 := by unfold GOther; decide
      exact slot_ne_g _ (loc_bound _ _ (by omega)) _ ho (hd.trans (congrArg Slot.g he))
    have hd16 : dest ≠ .x16 := by
      intro he
      exact slot_ne_g _ (loc_bound _ _ (by omega)) _ gother_temps.2.2.1 (hd.trans (congrArg Slot.g he))
    have hword : chiWord (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr .x16) (decide (x = 0 ∧ y = 0)) =
        out A (s.gpr .x16) x y := by
      have h0 := hb x hx (Or.inl rfl)
      have h1 := hb ((x + 1) % 5) (by omega) (Or.inr (Or.inl rfl))
      have h2 := hb ((x + 2) % 5) (by omega) (Or.inr (Or.inr rfl))
      simp only [ha, hb', hc, value] at h0 h1 h2
      simp only [chiWord, h0, h1, h2, out, decide_eq_true_eq]
    refine (chiInteger_ok s a b c dest _ ha17 hc17 hd0 hd16).mono fun s' ⟨hk, hv, ho⟩ => ?_
    refine ⟨hk, fun _ => by simp only [value, hv], fun j hj => ?_, fun i hi => ?_⟩
    · rw [ho _ (saved_ne_x17 _ _), ite_eq_right ?_]
      rw [← hd]
      exact saved_ne_state _ j _ hj (loc_bound _ _ (by omega))
    · rw [ho _ (slot_ne_g _ (loc_bound _ _ hi) _ gother_temps.2.2.2), hword]
      simp only [← hd, rowSlot_inj r x y i hx hy hi]
  all_goals exact hvec

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.FullRound

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid

theorem laneSlot_ne_x0 (i : Nat) (hi : i < 25) : laneSlot i ≠ .g .x0 := by
  have h : GOther .x0 := by unfold GOther; decide
  exact slot_ne_g i hi _ h

theorem loadLane_ok (s : VG.AArch64.State) (i : Nat) (hi : i < 25)
    (hin : InRegions (s.rd ++ s.wr) (laneAddr (s.gpr .x0) i) 8) :
    WP isa (.block (loadLane i)) s fun s' =>
      Keep s s' ∧ ∀ j < 25, value s' (laneSlot j) = if j = i
        then s.mem.readW (laneAddr (s.gpr .x0) i) 64 else value s (laneSlot j) := by
  unfold loadLane
  cases he : laneSlot i with
  | v v =>
    refine WP.cons (exec_ldr_x ⟨by omega, by omega⟩ hin) (WP.cons rfl (wp_nil ?_))
    refine ⟨?_, fun j hj => ?_⟩
    · constructor <;> simp (config := {decide := true}) only [RegUpd.gpr_setV, RegUpd.gpr_write,
        ite_false, RegUpd.mem_setV, RegUpd.mem_write, RegUpd.rd_setV, RegUpd.rd_write,
        RegUpd.wr_setV, RegUpd.wr_write, RegUpd.sp_setV, RegUpd.sp_write]
    · simp only [value_setV, vdword_ofVDwords_0, RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq,
        value_write, slot_ne_g j hj _ gother_temps.2.2.2, ite_false]
      have hji : laneSlot j = .v v ↔ j = i := by
        rw [← he]
        exact ⟨slot_inj j hj i hi, congrArg laneSlot⟩
      simp only [hji]
  | g g =>
    have hg0 : g ≠ .x0 := fun h => laneSlot_ne_x0 i hi (he.trans (congrArg Slot.g h))
    have hg16 : g ≠ .x16 := fun h =>
      slot_ne_g i hi _ gother_temps.2.2.1 (he.trans (congrArg Slot.g h))
    refine WP.cons (exec_ldr_x ⟨by omega, by omega⟩ hin) (wp_nil ?_)
    refine ⟨?_, fun j hj => ?_⟩
    · constructor <;> simp only [RegUpd.gpr_write, Ne.symm hg0, Ne.symm hg16, ite_false,
        RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write]
    · rw [value_write]
      have hji : laneSlot j = .g g ↔ j = i := by
        rw [← he]
        exact ⟨slot_inj j hj i hi, congrArg laneSlot⟩
      simp only [hji]

def LoadInv (s₀ : VG.AArch64.State) (n : Nat) (s : VG.AArch64.State) : Prop :=
  Keep s₀ s ∧ ∀ i < n, value s (laneSlot i) = s₀.mem.readW (laneAddr (s₀.gpr .x0) i) 64

theorem load_ok (s₀ : VG.AArch64.State) (hp : Pre s₀) :
    WP isa (.block load) s₀ fun s' =>
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.mem = s₀.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      Lanes s' 0 (Spec.Sha3.stateAt s₀.mem (s₀.gpr .x0)) := by
  have hh : WP isa (.block load) s₀ (LoadInv s₀ 25) := by
    refine wp_range_flatMap (M := isa) (LoadInv s₀) (fun i s hi ⟨hk, hl⟩ => ?_)
      25 (Nat.le_refl _) s₀ ⟨Keep.refl _, fun _ h => absurd h (by omega)⟩
    refine (loadLane_ok s i hi (by
      rw [hk.rd, hk.wr, hk.x0]; exact hp.in_all (hp.lane_in (i := i) (.inl rfl) hi))).mono
      fun s' ⟨hh, hv⟩ => ⟨hk.trans hh, fun j hj => ?_⟩
    rw [hv j (by omega)]
    by_cases he : j = i
    · subst j
      simp only [ite_true, hk.mem, hk.x0]
    · rw [ite_eq_right he, hl j (by omega)]
  exact hh.mono fun s' ⟨hk, hl⟩ => ⟨hk.x0, hk.mem, hk.rd, hk.wr, hk.sp, fun i hi => by
    simpa only [loc, Spec.Sha3.stateAt, Vector.getElem_ofFn] using hl i hi⟩

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

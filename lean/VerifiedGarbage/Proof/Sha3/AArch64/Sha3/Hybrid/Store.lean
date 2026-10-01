import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Load

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid

structure StoreKeep (s s' : VG.AArch64.State) : Prop where
  ptr : s'.gpr .x0 = s.gpr .x0
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lanes : ∀ i < 25, value s' (laneSlot i) = value s (laneSlot i)

theorem StoreKeep.refl (s : VG.AArch64.State) : StoreKeep s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
theorem StoreKeep.trans {s s' s'' : VG.AArch64.State} (h : StoreKeep s s') (h' : StoreKeep s' s'') :
    StoreKeep s s'' := ⟨h'.ptr.trans h.ptr, h'.wr.trans h.wr, h'.sp.trans h.sp,
      fun i hi => (h'.lanes i hi).trans (h.lanes i hi)⟩

theorem storeLane_ok (s : VG.AArch64.State) (i : Nat) (hi : i < 25)
    (hout : InRegions s.wr (laneAddr (s.gpr .x0) i) 8) :
    WP isa (.block (storeLane i)) s fun s' =>
      StoreKeep s s' ∧ s'.mem = s.mem.write (laneAddr (s.gpr .x0) i) 8 (value s (laneSlot i)) := by
  unfold storeLane
  cases he : laneSlot i with
  | v v =>
    refine WP.cons (exec_umov_low s .x17 v) (WP.cons (exec_str_x ⟨by omega, by omega⟩ ?_) (wp_nil ?_))
    · simpa (config := {decide := true}) only [RegUpd.wr_write, RegUpd.gpr_write, ite_false] using hout
    · refine ⟨⟨?_, rfl, rfl, ?_⟩, ?_⟩
      · simp (config := {decide := true}) only [RegUpd.gpr_write, ite_false]
      · intro j hj
        change value (s.write .x .x17 (vdword (s.v v) 0)) (laneSlot j) = _
        rw [value_write, ite_eq_right (slot_ne_g j hj _ gother_temps.2.2.2)]
      · simp (config := {decide := true}) only [value, RegUpd.gpr_write,
          RegUpd.mem_write, ite_true, ite_false, Size.bits, BitVec.setWidth_eq]
        rfl
  | g g =>
    refine WP.cons (exec_str_x ⟨by omega, by omega⟩ hout) (wp_nil ?_)
    exact ⟨⟨rfl, rfl, rfl, fun _ _ => rfl⟩, by simp only [value]; rfl⟩

structure StoreInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : StoreKeep s₀ s
  mem : ∀ i < k, s.mem.readW (laneAddr (s₀.gpr .x0) i) 64 = value s₀ (laneSlot i)

theorem store_ok (s₀ : VG.AArch64.State) (A : Spec.Sha3.State) (ha : Lanes s₀ 24 A)
    (hout : ∀ i < 25, InRegions s₀.wr (laneAddr (s₀.gpr .x0) i) 8) :
    WP isa (.block store) s₀ fun s' =>
      s'.sp = s₀.sp ∧ Spec.Sha3.stateAt s'.mem (s₀.gpr .x0) = A := by
  have hh : WP isa (.block store) s₀ (StoreInv s₀ 25) := by
    refine wp_range_flatMap (M := isa) (StoreInv s₀) (fun i s hi hs => ?_)
      25 (Nat.le_refl _) s₀ ⟨StoreKeep.refl _, fun _ h => absurd h (by omega)⟩
    refine (storeLane_ok s i hi (by rw [hs.keep.wr, hs.keep.ptr]; exact hout i hi)).mono
      fun s' ⟨hk, hm⟩ => ⟨hs.keep.trans hk, fun j hj => ?_⟩
    rw [hm, hs.keep.ptr]
    change (s.mem.writeW (laneAddr (s₀.gpr .x0) i) (value s (laneSlot i))).readW _ 64 = _
    by_cases he : j = i
    · subst j
      rw [Mem.readW_writeW_self64, hs.keep.lanes i hi]
    · rw [Mem.readW_writeW_sep (lane_sep (s₀.gpr .x0) (by omega) hi he) (by decide), hs.mem j (by omega)]
  refine hh.mono fun s' hs => ⟨hs.keep.sp, ?_⟩
  apply Vector.ext
  intro i hi
  simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn, hs.mem i hi]
  have h := ha i hi
  rwa [loc24 i hi] at h

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

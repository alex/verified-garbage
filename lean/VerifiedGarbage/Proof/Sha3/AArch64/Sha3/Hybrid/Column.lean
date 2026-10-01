import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Location

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid
open VG.Proof.Sha3 (C D B)

theorem value_congr {s s' : VG.AArch64.State} (a : Slot)
    (hv : ∀ v, a = .v v → vdword (s'.v v) 0 = vdword (s.v v) 0)
    (hg : ∀ g, a = .g g → s'.gpr g = s.gpr g) : value s' a = value s a := by
  cases a with
  | v v => exact hv v rfl
  | g g => exact hg g rfl

theorem columnSlow_ok (r x : Nat) (hx : x < 5) (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (ha : Lanes s r A) :
    WP isa (.block (columnSlow r x)) s fun s' =>
      s'.gpr (creg x) = C A x ∧ Keep s s' ∧
      (∀ g, g ≠ creg x → s'.gpr g = s.gpr g) ∧
      (∀ i < 25, value s' (laneSlot i) = value s (laneSlot i)) := by
  have hv28 : ∀ i, laneSlot i ≠ .v .v28 := fun i => slot_ne_v i _ vother_temps.1
  have hv29 : ∀ i, laneSlot i ≠ .v .v29 := fun i => slot_ne_v i _ vother_temps.2.1
  have hv30 : ∀ i, laneSlot i ≠ .v .v30 := fun i => slot_ne_v i _ vother_temps.2.2.1
  have hl : ∀ i (hi : i < 25), vdword (vector s (laneSlot (loc r i))) 0 = A[i]! :=
    fun i hi => (vector_low s _).trans ((ha i hi).trans (getElem!_eq A hi).symm)
  apply WP.of_runBlock
  simp (config := {decide := true}) (disch := first
    | exact hv28 _
    | exact hv29 _
    | exact hv30 _) only
    [columnSlow, List.append_assoc, List.cons_append, List.nil_append, readSlot_step,
      runBlock_cons, runStep_some, runBlock_nil, exec_vop, VOp.eval, exec_umov_low, isa,
      vector_loaded, vector_setV, loaded_v, RegUpd.v_setV, Option.map_some, Option.some.injEq, exists_eq_left', ite_true, ite_false]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, low_xor, hl, C]
  · have hc := creg_other x hx
    constructor <;> simp only [RegUpd.gpr_write, Ne.symm hc.1, Ne.symm hc.2, ite_false,
      loaded_gpr, loaded_mem, loaded_rd, loaded_wr, loaded_sp, RegUpd.gpr_setV, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
      RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV]
  · intro g hg
    simp only [RegUpd.gpr_write, hg, ite_false, loaded_gpr, RegUpd.gpr_setV]
  · intro i hi
    simp (disch := first | exact hv28 i | exact hv29 i | exact hv30 i) only [value_write, slot_ne_g i hi _ (gother_creg x hx), value_setV, value_loaded,
      hv28 i, ite_false]

theorem mixedColumn_ok (x : Nat) (hx : x < 5) (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (a b c d : VReg) (g : VG.AArch64.Reg) (hd : d ≠ .v28) (hg : g ≠ creg x)
    (hC : ((vdword (s.v a) 0 ^^^ vdword (s.v b) 0 ^^^ vdword (s.v c) 0) ^^^
      vdword (s.v d) 0) ^^^ s.gpr g = C A x) :
    WP isa (.block (mixedColumn a b c d g (creg x))) s fun s' =>
      s'.gpr (creg x) = C A x ∧ Keep s s' ∧
      (∀ g, g ≠ creg x → s'.gpr g = s.gpr g) ∧
      (∀ i < 25, value s' (laneSlot i) = value s (laneSlot i)) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mixedColumn, runBlock_cons, runBlock_nil, exec_vop,
    VOp.eval, exec_umov_low, exec_logic, State.read, Option.map_some, isa, runStep_some,
    Option.some.injEq, exists_eq_left', RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.gpr_write,
    hg, hd, ite_true, ite_false, Size.bits, BitVec.setWidth_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [low_xor] using hC
  · have hc := creg_other x hx
    constructor <;> simp only [RegUpd.gpr_write, Ne.symm hc.1, Ne.symm hc.2, ite_false,
      RegUpd.gpr_setV, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
      RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV]
  · intro g hg
    simp only [hg, ite_false]
  · intro i hi
    simp only [value_write, slot_ne_g i hi _ (gother_creg x hx), value_setV,
      slot_ne_v i _ vother_temps.1, ite_false]

theorem vectorColumn_ok (x : Nat) (hx : x < 5) (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (a b c d e : VReg) (hd : d ≠ .v28) (he : e ≠ .v28)
    (hC : (vdword (s.v a) 0 ^^^ vdword (s.v b) 0 ^^^ vdword (s.v c) 0) ^^^
      vdword (s.v d) 0 ^^^ vdword (s.v e) 0 = C A x) :
    WP isa (.block (vectorColumn a b c d e (creg x))) s fun s' =>
      s'.gpr (creg x) = C A x ∧ Keep s s' ∧
      (∀ g, g ≠ creg x → s'.gpr g = s.gpr g) ∧
      (∀ i < 25, value s' (laneSlot i) = value s (laneSlot i)) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [vectorColumn, runBlock_cons, runBlock_nil, exec_vop,
    VOp.eval, exec_umov_low, Option.map_some, isa, runStep_some,
    Option.some.injEq, exists_eq_left', RegUpd.v_setV, hd, he, ite_true, ite_false]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, low_xor] using hC
  · have hc := creg_other x hx
    constructor <;> simp only [RegUpd.gpr_write, Ne.symm hc.1, Ne.symm hc.2, ite_false,
      RegUpd.gpr_setV, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
      RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.sp_setV]
  · intro g hg
    simp only [RegUpd.gpr_write, hg, ite_false, RegUpd.gpr_setV]
  · intro i hi
    simp only [value_write, slot_ne_g i hi _ (gother_creg x hx), value_setV,
      slot_ne_v i _ vother_temps.1, ite_false]

theorem integerColumn_ok (x : Nat) (hx : x < 5) (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (a b c d e : VG.AArch64.Reg) (hc : c ≠ creg x) (hd : d ≠ creg x) (he : e ≠ creg x)
    (hC : s.gpr a ^^^ s.gpr b ^^^ s.gpr c ^^^ s.gpr d ^^^ s.gpr e = C A x) :
    WP isa (.block (integerColumn a b c d e (creg x))) s fun s' =>
      s'.gpr (creg x) = C A x ∧ Keep s s' ∧
      (∀ g, g ≠ creg x → s'.gpr g = s.gpr g) ∧
      (∀ i < 25, value s' (laneSlot i) = value s (laneSlot i)) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [integerColumn, runBlock_cons, runBlock_nil,
    exec_logic, State.read, isa, runStep_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, hc, hd, he, ite_true, ite_false, Size.bits, BitVec.setWidth_eq]
  refine ⟨hC, ?_, ?_, ?_⟩
  · have ho := creg_other x hx
    constructor <;> simp only [RegUpd.gpr_write, Ne.symm ho.1, Ne.symm ho.2, ite_false,
      RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write]
  · intro g hg
    simp only [hg, ite_false]
  · intro i hi
    simp only [value_write, slot_ne_g i hi _ (gother_creg x hx), ite_false]

theorem column_ok (r x : Nat) (hx : x < 5) (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (ha : Lanes s r A) :
    WP isa (.block (column r x)) s fun s' =>
      s'.gpr (creg x) = C A x ∧ Keep s s' ∧
      (∀ g, g ≠ creg x → s'.gpr g = s.gpr g) ∧
      (∀ i < 25, value s' (laneSlot i) = value s (laneSlot i)) := by
  have hslow := columnSlow_ok r x hx s A ha
  have h0 := (ha x (by omega)).trans (getElem!_eq A (by omega)).symm
  have h1 := (ha (x + 5) (by omega)).trans (getElem!_eq A (by omega)).symm
  have h2 := (ha (x + 10) (by omega)).trans (getElem!_eq A (by omega)).symm
  have h3 := (ha (x + 15) (by omega)).trans (getElem!_eq A (by omega)).symm
  have h4 := (ha (x + 20) (by omega)).trans (getElem!_eq A (by omega)).symm
  have hn : ∀ i < 25, laneSlot (loc r i) ≠ .v .v28 ∧ laneSlot (loc r i) ≠ .g (creg x) :=
    fun i hi => ⟨slot_ne_v _ _ vother_temps.1, slot_ne_g _ (loc_bound _ _ hi) _ (gother_creg x hx)⟩
  have hn0 := hn x (by omega)
  have hn1 := hn (x + 5) (by omega)
  have hn2 := hn (x + 10) (by omega)
  have hn3 := hn (x + 15) (by omega)
  have hn4 := hn (x + 20) (by omega)
  unfold column
  cases hq0 : laneSlot (loc r x) <;> cases hq1 : laneSlot (loc r (x + 5)) <;>
    cases hq2 : laneSlot (loc r (x + 10)) <;> cases hq3 : laneSlot (loc r (x + 15)) <;>
    cases hq4 : laneSlot (loc r (x + 20)) <;> first | exact hslow | skip
  all_goals
    simp only [hq0, hq1, hq2, hq3, hq4, value] at h0 h1 h2 h3 h4
    simp only [hq0, hq1, hq2, hq3, hq4, ne_eq, Slot.v.injEq, Slot.g.injEq,
      reduceCtorEq, not_false_eq_true, and_true, true_and] at hn0 hn1 hn2 hn3 hn4
    first
    | apply vectorColumn_ok x hx s A
    | apply integerColumn_ok x hx s A
    | apply mixedColumn_ok x hx s A
    all_goals first | assumption | (rw [h0, h1, h2, h3, h4]; simp only [C] <;> ac_rfl)

def ColInv (s₀ : VG.AArch64.State) (r : Nat) (A : Spec.Sha3.State) (k : Nat)
    (s : VG.AArch64.State) : Prop :=
  Keep s₀ s ∧ Lanes s r A ∧ ∀ x < k, s.gpr (creg x) = C A x

theorem columns_ok (r : Nat) (s₀ : VG.AArch64.State) (A : Spec.Sha3.State) (ha : Lanes s₀ r A) :
    WP isa (.block ((List.range 5).flatMap (column r))) s₀ (ColInv s₀ r A 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ r A) (fun x s hx ⟨hs, hA, hc⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Keep.refl _, ha, fun _ h => absurd h (by omega)⟩
  refine (column_ok r x hx s A hA).mono fun s' ⟨hv, hh, hg, hl⟩ => ?_
  refine ⟨hs.trans hh, fun i hi => ?_, fun j hj => ?_⟩
  · rw [hl _ (loc_bound _ _ hi)]
    exact hA i hi
  · by_cases he : j = x
    · subst he; exact hv
    · rw [hg _ (fun e => he (creg_inj _ (by omega) _ hx e)), hc j (by omega)]

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

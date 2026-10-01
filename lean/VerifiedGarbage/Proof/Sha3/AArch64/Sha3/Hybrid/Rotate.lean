import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Column

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid
open VG.Impl.Sha3 (rhoOff)
open VG.Proof.Sha3 (C D B)

def rotVector (a b : BitVec 128) (sh : Nat) : BitVec 128 :=
  VArr.map2 .d2 (fun _ x y => (x ^^^ y).rotateRight sh) a b

theorem rotVector_low (a b : BitVec 128) (sh : Nat) :
    vdword (rotVector a b sh) 0 = (vdword a 0 ^^^ vdword b 0).rotateRight sh := by
  simp only [rotVector, VArr.map2, vdword_ofVDwords_0]

def rotated (s : VG.AArch64.State) (a : Slot) (sh : Nat) : VG.AArch64.State :=
  match a with
  | .v v => s.setV v (rotVector (s.v v) (s.v .v28) sh)
  | .g g =>
    let z := s.gpr g ^^^ s.gpr .x17
    (s.write .x g z).write .x g (z.rotateRight sh)

theorem rotateSlot_step (s : VG.AArch64.State) (a : Slot) (sh : Nat) (hs : sh < 64)
    (rest : List Instr) :
    runBlock isa (rotateSlot a sh ++ rest) s = runBlock isa rest (rotated s a sh) := by
  cases a with
  | v v => simp only [rotateSlot, rotated, rotVector, List.cons_append, List.nil_append,
      runBlock_cons, exec_vop, VOp.eval, hs, ite_true, Option.map_some, isa, runStep_some]
  | g g =>
    simp only [rotateSlot, rotated, List.cons_append, List.nil_append, runBlock_cons,
      exec_logic, exec_ror_x hs, isa, runStep_some,
      RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq]

theorem rotated_value (s : VG.AArch64.State) (a b : Slot) (sh : Nat) (hd : s.gpr .x17 = vdword (s.v .v28) 0) :
    value (rotated s a sh) b =
      if b = a then (value s a ^^^ vdword (s.v .v28) 0).rotateRight sh else value s b := by
  cases a with
  | v v =>
    simp only [rotated, value_setV, rotVector_low]
    rfl
  | g g =>
    simp only [rotated, value_write, hd]
    split <;> rfl

theorem rotated_keep (s : VG.AArch64.State) (i : Nat) (hi : i < 25) (sh : Nat) :
    Keep s (rotated s (laneSlot i) sh) := by
  have hx : ∀ i < 5, greg i ≠ .x0 ∧ greg i ≠ .x16 := by decide
  unfold laneSlot
  split <;> simp only [rotated]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hg := hx (i - 20) (by omega)
    constructor <;> simp only [RegUpd.gpr_write, Ne.symm hg.1, Ne.symm hg.2, ite_false,
      RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write]

theorem rotated_c (s : VG.AArch64.State) (i x : Nat) (hi : i < 25) (hx : x < 5) (sh : Nat) :
    (rotated s (laneSlot i) sh).gpr (creg x) = s.gpr (creg x) := by
  unfold laneSlot
  split <;> simp only [rotated]
  · rfl
  · simp only [RegUpd.gpr_write, Ne.symm (gother_creg x hx (i - 20) (by omega)),
      ite_false]

theorem rotated_d (s : VG.AArch64.State) (i : Nat) (sh : Nat) :
    (rotated s (laneSlot i) sh).v .v28 = s.v .v28 := by
  unfold laneSlot
  split <;> simp only [rotated]
  · simp only [RegUpd.v_setV, Ne.symm (vother_temps.1 i (by assumption)), ite_false]
  · rfl

theorem rotated_x17 (s : VG.AArch64.State) (i : Nat) (hi : i < 25) (sh : Nat) :
    (rotated s (laneSlot i) sh).gpr .x17 = s.gpr .x17 := by
  unfold laneSlot
  split <;> simp only [rotated]
  · rfl
  · simp only [RegUpd.gpr_write, Ne.symm (gother_temps.2.2.2 (i - 20) (by omega)), ite_false]

theorem rotateLane_ok (r x y : Nat) (hx : x < 5) (hy : y < 5) (s : VG.AArch64.State)
    (hd : s.gpr .x17 = vdword (s.v .v28) 0) :
    WP isa (.block (rotateLane r x y)) s fun s' =>
      Keep s s' ∧ s'.v .v28 = s.v .v28 ∧ s'.gpr .x17 = s.gpr .x17 ∧
      (∀ j < 5, s'.gpr (creg j) = s.gpr (creg j)) ∧
      ∀ i < 25, value s' (laneSlot (loc r i)) = if i = x + 5 * y
        then Proof.Sha3.rotl (value s (laneSlot (loc r i)) ^^^ vdword (s.v .v28) 0) (rhoOff i)
        else value s (laneSlot (loc r i)) := by
  have hi : x + 5 * y < 25 := by omega
  have hl := loc_bound r _ hi
  apply WP.of_runBlock
  rw [rotateLane, ← List.append_nil (rotateSlot _ _), rotateSlot_step _ _ _ (by omega), runBlock_nil]
  refine ⟨_, rfl, rotated_keep _ _ hl _, rotated_d _ _ _, rotated_x17 _ _ hl _, fun j hj => rotated_c _ _ _ hl hj _, ?_⟩
  intro i hi'
  rw [rotated_value _ _ _ _ hd]
  have he : laneSlot (loc r i) = laneSlot (loc r (x + 5 * y)) ↔ i = x + 5 * y :=
    ⟨fun h => loc_inj r _ _ hi' hi (slot_inj _ (loc_bound _ _ hi') _ hl h),
      fun h => congrArg (fun j => laneSlot (loc r j)) h⟩
  simp only [he]
  split
  · rename_i h; subst i
    exact rotl_mod _ _ (rhoOff_lt _ hi)
  · rfl

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

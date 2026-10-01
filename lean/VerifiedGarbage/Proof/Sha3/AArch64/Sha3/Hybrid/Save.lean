import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Chi

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid

def saved (s : VG.AArch64.State) (a : Slot) (i : Nat) : VG.AArch64.State := match a with
  | .v v => s.setV (if i = 0 then .v28 else .v29) (s.v v)
  | .g g => s.write .x (if i = 0 then .x14 else .x15) (s.gpr g)

theorem saveSlot_step (s : VG.AArch64.State) (a : Slot) (i : Nat) (rest : List Instr) :
    runBlock isa (saveSlot a i ++ rest) s = runBlock isa rest (saved s a i) := by
  cases a <;> simp only [saveSlot, saved, List.cons_append, List.nil_append,
    VG.Impl.Sha3.AArch64.mov, runBlock_cons, exec_vop, VOp.eval,
    exec_addImm_x (by decide : 0 < 4096), BitVec.add_zero,
    Option.map_some, isa, runStep_some, State.read, Size.bits, BitVec.setWidth_eq]

theorem saved_value (s : VG.AArch64.State) (a b : Slot) (i : Nat) :
    value (saved s a i) b = if b = savedSlot a i then value s a else value s b := by
  cases a <;> simp only [saved, savedSlot, value_setV, value_write] <;> rfl

theorem saved_keep (s : VG.AArch64.State) (a : Slot) (i : Nat) : Keep s (saved s a i) := by
  cases a with
  | v _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | g _ =>
    simp only [saved]
    split <;> constructor <;>
      simp (config := {decide := true}) only [RegUpd.gpr_write, ite_false,
        RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write]

theorem saved_distinct (a b : Slot) : savedSlot a 0 ≠ savedSlot b 1 := by
  cases a <;> cases b <;> simp (config := {decide := true}) only [savedSlot, ite_true, ite_false]

theorem save_pair_ok (r y : Nat) (hy : y < 5) (s : VG.AArch64.State) :
    WP isa (.block (saveSlot (rowSlot r 0 y) 0 ++ saveSlot (rowSlot r 1 y) 1)) s fun s' =>
      Keep s s' ∧ (∀ i < 25, value s' (laneSlot i) = value s (laneSlot i)) ∧
      ∀ j < 2, value s' (savedSlot (rowSlot r j y) j) = value s (rowSlot r j y) := by
  apply WP.of_runBlock
  rw [saveSlot_step, ← List.append_nil (saveSlot _ _), saveSlot_step, runBlock_nil]
  refine ⟨_, rfl, (saved_keep _ _ _).trans (saved_keep _ _ _), ?_, ?_⟩
  · intro i hi
    rw [saved_value, ite_eq_right (saved_ne_state _ 1 i (by decide) hi).symm,
      saved_value, ite_eq_right (saved_ne_state _ 0 i (by decide) hi).symm]
  · intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with h | h <;> subst j
    · rw [saved_value, ite_eq_right (saved_distinct _ _), saved_value, ite_eq_left rfl]
    · rw [saved_value, ite_eq_left rfl, saved_value]
      exact ite_eq_right (saved_ne_state _ 0 _ (by decide)
        (loc_bound (r + 1) (1 + 5 * y) (by omega))).symm

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

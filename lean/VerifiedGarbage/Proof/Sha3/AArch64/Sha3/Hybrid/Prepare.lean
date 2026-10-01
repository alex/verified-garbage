import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Rho

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid

def prepared (s : VG.AArch64.State) (a : Slot) (t : VReg) : VG.AArch64.State := match a with
  | .v _ => s
  | .g g => s.setV t (ofVDwords (s.gpr g) (s.gpr g))

theorem prepare_step (s : VG.AArch64.State) (a : Slot) (t : VReg) (rest : List Instr) :
    runBlock isa (prepare a t ++ rest) s = runBlock isa rest (prepared s a t) := by
  cases a <;> simp only [prepare, prepared, List.cons_append, List.nil_append,
    runBlock_cons, exec_vop, VOp.eval, Option.map_some, isa, runStep_some]

theorem prepared_low (s : VG.AArch64.State) (a : Slot) (t : VReg) :
    vdword ((prepared s a t).v (operand a t)) 0 = value s a := by
  cases a <;> simp only [prepared, operand, value, RegUpd.v_setV, ite_true, vdword_ofVDwords_0]

theorem prepared_v (s : VG.AArch64.State) (a : Slot) (t v : VReg)
    (h : isGpr a = true → v ≠ t) : (prepared s a t).v v = s.v v := by
  cases a with
  | v _ => rfl
  | g _ => simp only [prepared, RegUpd.v_setV, h rfl, ite_false]

theorem prepared_value (s : VG.AArch64.State) (a b : Slot) (t : VReg)
    (h : isGpr a = true → b ≠ .v t) : value (prepared s a t) b = value s b := by
  cases a with
  | v _ => rfl
  | g _ => simp only [prepared, value_setV, h rfl, ite_false]

theorem prepared_gpr (s : VG.AArch64.State) (a : Slot) (t : VReg) :
    (prepared s a t).gpr = s.gpr := by cases a <;> rfl

theorem prepared_keep (s : VG.AArch64.State) (a : Slot) (t : VReg) : Keep s (prepared s a t) := by
  cases a <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem prepared_mem (s : VG.AArch64.State) (a : Slot) (t : VReg) :
    (prepared s a t).mem = s.mem := by cases a <;> rfl
theorem prepared_rd (s : VG.AArch64.State) (a : Slot) (t : VReg) :
    (prepared s a t).rd = s.rd := by cases a <;> rfl
theorem prepared_wr (s : VG.AArch64.State) (a : Slot) (t : VReg) :
    (prepared s a t).wr = s.wr := by cases a <;> rfl
theorem prepared_sp (s : VG.AArch64.State) (a : Slot) (t : VReg) :
    (prepared s a t).sp = s.sp := by cases a <;> rfl

/-- Each input must survive preparations of the other two inputs. -/
structure PrepSafe (a b c : Slot) (ta tb tc : VReg) : Prop where
  ab : isGpr a = true → b ≠ .v ta
  ac : isGpr a = true → c ≠ .v ta
  bc : isGpr b = true → c ≠ .v tb
  ba : isGpr b = true → operand a ta ≠ tb
  ca : isGpr c = true → operand a ta ≠ tc
  cb : isGpr c = true → operand b tb ≠ tc

instance (a b c : Slot) (ta tb tc : VReg) : Decidable (PrepSafe a b c ta tb tc) :=
  if h : (isGpr a = true → b ≠ .v ta) ∧ (isGpr a = true → c ≠ .v ta) ∧
      (isGpr b = true → c ≠ .v tb) ∧ (isGpr b = true → operand a ta ≠ tb) ∧
      (isGpr c = true → operand a ta ≠ tc) ∧ (isGpr c = true → operand b tb ≠ tc) then
    isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  else isFalse (fun h' => h ⟨h'.ab, h'.ac, h'.bc, h'.ba, h'.ca, h'.cb⟩)

abbrev preps (s : VG.AArch64.State) (a b c : Slot) (ta tb tc : VReg) : VG.AArch64.State :=
  prepared (prepared (prepared s a ta) b tb) c tc

theorem preps_inputs (s : VG.AArch64.State) (a b c : Slot) (ta tb tc : VReg)
    (h : PrepSafe a b c ta tb tc) :
    vdword ((preps s a b c ta tb tc).v (operand a ta)) 0 = value s a ∧
    vdword ((preps s a b c ta tb tc).v (operand b tb)) 0 = value s b ∧
    vdword ((preps s a b c ta tb tc).v (operand c tc)) 0 = value s c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [prepared_v _ _ _ _ h.ca, prepared_v _ _ _ _ h.ba, prepared_low]
  · rw [prepared_v _ _ _ _ h.cb, prepared_low, prepared_value _ _ _ _ h.ab]
  · rw [prepared_low, prepared_value _ _ _ _ h.bc, prepared_value _ _ _ _ h.ac]

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

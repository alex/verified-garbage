import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Common
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Hybrid

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid
open VG.Impl.Sha3 (piSrc)

theorem pi_bound (i : Nat) : piSrc (i % 5) (i / 5) < 25 := by
  unfold piSrc
  omega

theorem pi_inj : ∀ i < 25, ∀ j < 25,
    piSrc (i % 5) (i / 5) = piSrc (j % 5) (j / 5) → i = j := by decide

theorem loc_bound (r i : Nat) (hi : i < 25) : loc r i < 25 := by
  induction r generalizing i with
  | zero => exact hi
  | succ r ih => exact ih _ (pi_bound i)

theorem loc_inj (r i j : Nat) (hi : i < 25) (hj : j < 25) (h : loc r i = loc r j) : i = j := by
  induction r generalizing i j with
  | zero => exact h
  | succ r ih => exact pi_inj i hi j hj (ih _ _ (pi_bound i) (pi_bound j) h)

theorem loc24 : ∀ i < 25, loc 24 i = i := by decide

theorem loc_succ (r x y : Nat) (hx : x < 5) :
    loc (r + 1) (x + 5 * y) = loc r (piSrc x y) := by
  simp only [loc, show (x + 5 * y) % 5 = x by omega, show (x + 5 * y) / 5 = y by omega]

def value (s : VG.AArch64.State) : Slot → BitVec 64
  | .v v => vdword (s.v v) 0
  | .g g => s.gpr g

def vector (s : VG.AArch64.State) : Slot → BitVec 128
  | .v v => s.v v
  | .g g => ofVDwords (s.gpr g) (s.gpr g)

theorem vector_low (s : VG.AArch64.State) (a : Slot) : vdword (vector s a) 0 = value s a := by
  cases a with
  | v v => rfl
  | g g => exact vdword_ofVDwords_0 _ _

def Lanes (s : VG.AArch64.State) (r : Nat) (A : Spec.Sha3.State) : Prop :=
  ∀ i (hi : i < 25), value s (laneSlot (loc r i)) = A[i]

def VOther (v : VReg) : Prop := ∀ i < 20, vreg i ≠ v
def GOther (g : VG.AArch64.Reg) : Prop := ∀ i < 5, greg i ≠ g

theorem vother_temps : VOther .v28 ∧ VOther .v29 ∧ VOther .v30 ∧ VOther .v31 := by unfold VOther; decide
theorem gother_creg : ∀ x < 5, GOther (creg x) := by unfold GOther; decide
theorem gother_temps : GOther .x14 ∧ GOther .x15 ∧ GOther .x16 ∧ GOther .x17 := by unfold GOther; decide
theorem creg_inj : ∀ i < 5, ∀ j < 5, creg i = creg j → i = j := by decide
theorem creg_other : ∀ i < 5, creg i ≠ .x0 ∧ creg i ≠ .x16 := by decide
theorem slot_inj : ∀ i < 25, ∀ j < 25, laneSlot i = laneSlot j → i = j := by decide

theorem value_setV (s : VG.AArch64.State) (d : VReg) (v : BitVec 128) (a : Slot) :
    value (s.setV d v) a = if a = .v d then vdword v 0 else value s a := by
  cases a <;> simp only [value, RegUpd.v_setV, RegUpd.gpr_setV, Slot.v.injEq,
    reduceCtorEq, ite_false]
  split <;> rfl

theorem value_write (s : VG.AArch64.State) (d : VG.AArch64.Reg) (v : BitVec 64) (a : Slot) :
    value (s.write .x d v) a = if a = .g d then v else value s a := by
  cases a <;> simp only [value, RegUpd.v_write, RegUpd.gpr_write, Slot.g.injEq,
    reduceCtorEq, ite_false, Size.bits, BitVec.setWidth_eq]

theorem slot_ne_v (i : Nat) (d : VReg) (hd : VOther d) : laneSlot i ≠ .v d := by
  unfold laneSlot
  split
  · simp only [ne_eq, Slot.v.injEq]; exact hd i (by assumption)
  · exact Slot.noConfusion

theorem slot_ne_g (i : Nat) (hi : i < 25) (d : VG.AArch64.Reg) (hd : GOther d) : laneSlot i ≠ .g d := by
  unfold laneSlot
  split
  · exact Slot.noConfusion
  · simp only [ne_eq, Slot.g.injEq]; exact hd (i - 20) (by omega)

theorem vector_setV (s : VG.AArch64.State) (d : VReg) (v : BitVec 128) (a : Slot)
    (ha : a ≠ .v d) : vector (s.setV d v) a = vector s a := by
  cases a with
  | v r => simp only [ne_eq, Slot.v.injEq] at ha; simp only [vector, RegUpd.v_setV, ha, ite_false]
  | g r => rfl

theorem vector_write (s : VG.AArch64.State) (d : VG.AArch64.Reg) (v : BitVec 64) (a : Slot)
    (ha : a ≠ .g d) : vector (s.write .x d v) a = vector s a := by
  cases a with
  | v r => rfl
  | g r => simp only [ne_eq, Slot.g.injEq] at ha; simp only [vector, RegUpd.gpr_write, ha, ite_false]

def loaded (s : VG.AArch64.State) (d : VReg) (a : Slot) : VG.AArch64.State := s.setV d (vector s a)

theorem loaded_v (s : VG.AArch64.State) (d v : VReg) (a : Slot) :
    (loaded s d a).v v = if v = d then vector s a else s.v v := RegUpd.v_setV _ _ _ _
theorem loaded_gpr (s : VG.AArch64.State) (d : VReg) (a : Slot) : (loaded s d a).gpr = s.gpr := rfl
theorem loaded_mem (s : VG.AArch64.State) (d : VReg) (a : Slot) : (loaded s d a).mem = s.mem := rfl
theorem loaded_rd (s : VG.AArch64.State) (d : VReg) (a : Slot) : (loaded s d a).rd = s.rd := rfl
theorem loaded_wr (s : VG.AArch64.State) (d : VReg) (a : Slot) : (loaded s d a).wr = s.wr := rfl
theorem loaded_sp (s : VG.AArch64.State) (d : VReg) (a : Slot) : (loaded s d a).sp = s.sp := rfl

theorem vector_loaded (s : VG.AArch64.State) (d : VReg) (a b : Slot) (hb : b ≠ .v d) :
    vector (loaded s d a) b = vector s b := vector_setV _ _ _ _ hb

theorem value_loaded (s : VG.AArch64.State) (d : VReg) (a b : Slot) (hb : b ≠ .v d) :
    value (loaded s d a) b = value s b := by
  dsimp only [loaded]
  rw [value_setV, ite_eq_right hb]

theorem readSlot_step (s : VG.AArch64.State) (d : VReg) (a : Slot) (rest : List Instr) :
    runBlock isa (readSlot d a ++ rest) s = runBlock isa rest (loaded s d a) := by
  cases a <;> simp only [readSlot, loaded, vector, List.cons_append, List.nil_append,
    runBlock_cons, exec_vop, VOp.eval, Option.map_some, isa, runStep_some]

structure Keep (s s' : VG.AArch64.State) : Prop where
  x0 : s'.gpr .x0 = s.gpr .x0
  x16 : s'.gpr .x16 = s.gpr .x16
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (s : VG.AArch64.State) : Keep s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s s' s'' : VG.AArch64.State} (h : Keep s s') (h' : Keep s' s'') : Keep s s'' :=
  ⟨h'.x0.trans h.x0, h'.x16.trans h.x16, h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

end VG.Proof.Sha3.AArch64.Sha3.Hybrid

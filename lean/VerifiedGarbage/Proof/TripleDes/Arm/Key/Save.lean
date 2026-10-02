import VerifiedGarbage.Proof.Rc2.Arm.Save
import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm VG.Impl.TripleDes.Arm

/-- The nine callee-saved registers, in slot order. -/
def savedReg (i : Nat) : Reg := (Impl.TripleDes.Arm.Key.savedRegs).getD i .r4

theorem save_eq : Impl.TripleDes.Arm.Key.save = VG.Proof.Rc2.Arm.saveCode .r3 savedReg 9 := by
  decide +kernel

theorem restore_eq : Impl.TripleDes.Arm.Key.restore = VG.Proof.Rc2.Arm.restoreCode .r3 savedReg (List.range 9) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 9, current.mem.readW (State.addr (current.gpr .r3) + BitVec.ofNat 64 (4 * i)) 32 =
    original.gpr (savedReg i)

theorem save_ok (s : State)
    (fit : (s.gpr .r3).toNat + 256 ≤ 2 ^ 32)
    (hw : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block Impl.TripleDes.Arm.Key.save) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Saved s s' ∧
      Frame [⟨State.addr (s.gpr .r3), 36⟩] s.mem s'.mem) := by
  rw [save_eq]
  apply WP.mono (VG.Proof.Rc2.Arm.saveCode_ok s .r3 savedReg 9 (by decide) fit hw)
  intro s' hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hs.1, hs.2.2.2]
    exact VG.Proof.Rc2.Arm.saveMem_read _ _ _ 9 (by decide) i hi
  · rw [hs.2.2.2]
    exact VG.Proof.Rc2.Arm.saveMem_frame _ _ _ 9 (by decide)

theorem savedReg_separate : ∀ i < 9, savedReg i ≠ .r3 := by decide +kernel

theorem restore_ok (original s : State) (hsaved : Saved original s)
    (fit : (s.gpr .r3).toNat + 256 ≤ 2 ^ 32)
    (hread : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r3) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block Impl.TripleDes.Arm.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.Arm.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.Arm.Keep (Impl.TripleDes.Arm.Key.savedRegs) s s') := by
  rw [restore_eq]
  have hregs : (List.range 9).map savedReg = Impl.TripleDes.Arm.Key.savedRegs := by decide +kernel
  have h := VG.Proof.Rc2.Arm.restoreCode_ok s .r3 savedReg (List.range 9) original.gpr fit
    (fun i hi => by have := List.mem_range.mp hi; omega)
    (fun i hi => savedReg_separate i (List.mem_range.mp hi))
    (fun i hi => hread i (List.mem_range.mp hi))
    (fun i hi => hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  exact h



end VG.Proof.TripleDes.Arm.Key

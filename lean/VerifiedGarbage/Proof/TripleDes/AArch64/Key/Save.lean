import VerifiedGarbage.Proof.Rc2.AArch64.Save
import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- The four callee-saved registers, in slot order. -/
def savedReg (i : Nat) : Reg := (Impl.TripleDes.AArch64.Key.savedRegs).getD i .x19

theorem save_eq : Impl.TripleDes.AArch64.Key.save = VG.Proof.Rc2.AArch64.saveCode .x3 savedReg 4 := by
  decide +kernel

theorem restore_eq : Impl.TripleDes.AArch64.Key.restore = VG.Proof.Rc2.AArch64.restoreCode .x3 savedReg (List.range 4) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 4, current.mem.readW (current.gpr .x3 + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

theorem save_ok (s : State)
    (hw : ∀ i < 4, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.AArch64.Key.save) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Saved s s' ∧
      Frame [⟨s.gpr .x3, 32⟩] s.mem s'.mem) := by
  rw [save_eq]
  apply WP.mono (VG.Proof.Rc2.AArch64.saveCode_ok s .x3 savedReg 4 (by decide) hw)
  intro s' hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hs.1, hs.2.2.2]
    exact VG.Proof.Rc2.AArch64.saveMem_read _ _ _ 4 (by decide) i hi
  · rw [hs.2.2.2]
    exact VG.Proof.Rc2.AArch64.saveMem_frame _ _ _ 4 (by decide)

theorem savedReg_separate : ∀ i < 4, savedReg i ≠ .x3 := by decide +kernel

theorem restore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.AArch64.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.AArch64.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.AArch64.Keep (Impl.TripleDes.AArch64.Key.savedRegs) s s') := by
  rw [restore_eq]
  have hregs : (List.range 4).map savedReg = Impl.TripleDes.AArch64.Key.savedRegs := by decide +kernel
  have h := VG.Proof.Rc2.AArch64.restoreCode_ok s .x3 savedReg (List.range 4) original.gpr
    (fun i hi => by have := List.mem_range.mp hi; omega)
    (fun i hi => savedReg_separate i (List.mem_range.mp hi))
    (fun i hi => hread i (List.mem_range.mp hi))
    (fun i hi => hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  exact h



end VG.Proof.TripleDes.AArch64.Key

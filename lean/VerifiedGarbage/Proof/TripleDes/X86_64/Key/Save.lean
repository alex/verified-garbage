import VerifiedGarbage.Proof.Rc2.X86_64.Save
import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- The six callee-saved registers, in slot order. -/
def savedReg (i : Nat) : Reg := (Impl.TripleDes.X86_64.Key.savedRegs).getD i .rdi

theorem save_eq : Impl.TripleDes.X86_64.Key.save = VG.Proof.Rc2.X86_64.saveCode .rcx savedReg 6 := by
  decide +kernel

theorem restore_eq : Impl.TripleDes.X86_64.Key.restore = VG.Proof.Rc2.X86_64.restoreCode .rcx savedReg (List.range 6) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 6, current.mem.readW (current.gpr .rcx + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

theorem save_ok (s : State)
    (hw : ∀ i < 6, InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.save) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Saved s s' ∧
      Frame [⟨s.gpr .rcx, 48⟩] s.mem s'.mem) := by
  rw [save_eq]
  apply WP.mono (VG.Proof.Rc2.X86_64.saveCode_ok s .rcx savedReg 6 hw)
  intro s' hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hs.1, hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_read _ _ _ 6 (by decide) i hi
  · rw [hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_frame _ _ _ 6 (by decide)

theorem savedReg_separate : ∀ i < 6, savedReg i ≠ .rcx := by decide +kernel

theorem restore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 6, InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.X86_64.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.X86_64.Keep (Impl.TripleDes.X86_64.Key.savedRegs) s s') := by
  rw [restore_eq]
  have hregs : (List.range 6).map savedReg = Impl.TripleDes.X86_64.Key.savedRegs := by decide +kernel
  have h := VG.Proof.Rc2.X86_64.restoreCode_ok s .rcx savedReg (List.range 6) original.gpr
    (fun i hi => savedReg_separate i (List.mem_range.mp hi))
    (fun i hi => hread i (List.mem_range.mp hi))
    (fun i hi => hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  exact h



end VG.Proof.TripleDes.X86_64.Key

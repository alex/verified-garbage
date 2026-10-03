import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- The four callee-saved registers, in slot order. -/
def savedReg (i : Nat) : Reg := (Impl.TripleDes.AArch64.Key.savedRegs).getD i .x19

theorem save_eq : Impl.TripleDes.AArch64.Key.save = Spill.saveCode .x3 (Spill.slots savedReg 4) := by
  decide +kernel

theorem restore_eq : Impl.TripleDes.AArch64.Key.restore = Spill.restoreCode .x3 (Spill.slots savedReg 4) := by
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
  refine WP.mono (Spill.save_wp (by decide) (Spill.forall_slots hw)) fun s' h =>
    ⟨h.gpr, h.rd, h.wr, fun i hi => ?_, ?_⟩
  · rw [h.gpr, h.mem]
    exact Spill.saveMem_saved (l := Spill.slots savedReg 4) (by decide) s.mem (s.gpr .x3) s.gpr
      (savedReg i, 8 * i) (Spill.mem_slots hi)
  · rw [h.mem]; exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem savedReg_separate : ∀ i < 4, savedReg i ≠ .x3 := by decide +kernel

theorem restore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.AArch64.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.AArch64.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.AArch64.Keep (Impl.TripleDes.AArch64.Key.savedRegs) s s') := by
  rw [restore_eq]
  have hregs : (Spill.slots savedReg 4).map Prod.fst = Impl.TripleDes.AArch64.Key.savedRegs := by
    decide +kernel
  exact WP.mono (Spill.restore_wp rfl (by decide) (by decide) (Spill.forall_slots hread)
    (Spill.forall_slots hsaved)) fun s' h =>
    ⟨fun r hr => h.gpr_of (.inl (hregs ▸ hr)), ⟨fun r hr => h.other r (hregs ▸ hr), h.mem, h.rd, h.wr⟩⟩

end VG.Proof.TripleDes.AArch64.Key

import VerifiedGarbage.Proof.Rc2.X86_64.Save
import VerifiedGarbage.Impl.TripleDes.X86_64.Block
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundStep

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- The six callee-saved registers and the schedule pointer, in slot order. -/
def savedReg (i : Nat) : Reg := (savedRegs ++ [Reg.rdi]).getD i .rdi

theorem blockSave_eq : blockSave = VG.Proof.Rc2.X86_64.saveCode .rdx savedReg 7 := by
  decide +kernel

theorem blockRestore_eq : blockRestore = VG.Proof.Rc2.X86_64.restoreCode .rdx savedReg (List.range 7) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 7, current.mem.readW (current.gpr .rdx + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

theorem blockSave_ok (s : State)
    (hw : ∀ i < 7, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockSave) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Saved s s' ∧
      Frame [⟨s.gpr .rdx, 56⟩] s.mem s'.mem) := by
  rw [blockSave_eq]
  apply WP.mono (VG.Proof.Rc2.X86_64.saveCode_ok s .rdx savedReg 7 hw)
  intro s' hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hs.1, hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_read _ _ _ 7 (by decide) i hi
  · rw [hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_frame _ _ _ 7 (by decide)

theorem savedReg_separate : ∀ i < 7, savedReg i ≠ .rdx := by decide +kernel

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 7, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockRestore) s (fun s' =>
      (∀ r ∈ savedRegs ++ [Reg.rdi], s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.X86_64.Keep (savedRegs ++ [Reg.rdi]) s s') := by
  rw [blockRestore_eq]
  have hregs : (List.range 7).map savedReg = savedRegs ++ [Reg.rdi] := by decide +kernel
  have h := VG.Proof.Rc2.X86_64.restoreCode_ok s .rdx savedReg (List.range 7) original.gpr
    (fun i hi => savedReg_separate i (List.mem_range.mp hi))
    (fun i hi => hread i (List.mem_range.mp hi))
    (fun i hi => hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  exact h


theorem savedSlot_work_disjoint (s : State) (i : Nat) (hi : i < 7) :
    (⟨s.gpr .rdx + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (workRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by omega) (by omega) (by decide)

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .rdx = s.gpr .rdx) (hf : Frame [workRegion s] s.mem t.mem) :
    Saved original t := by
  intro i hi
  have hmem := hf.readW (a := s.gpr .rdx + BitVec.ofNat 64 (8 * i)) (w := 64)
    (r := ⟨s.gpr .rdx + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact savedSlot_work_disjoint s i hi)
    (by decide)
  rw [hbase]
  exact hmem.trans (hs i hi)

end VG.Proof.TripleDes.X86_64

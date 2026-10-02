import VerifiedGarbage.Proof.Rc2.Arm.Save
import VerifiedGarbage.Proof.TripleDes.Arm.RoundStep

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm

def savedReg (i : Nat) : Reg := savedRegs.getD i .r4

theorem blockSave_eq : blockSave = VG.Proof.Rc2.Arm.saveCode .r2 savedReg 9 := by
  decide +kernel

theorem blockRestore_eq : blockRestore = VG.Proof.Rc2.Arm.restoreCode .r2 savedReg (List.range 9) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 9, current.mem.readW (State.addr (current.gpr .r2) + BitVec.ofNat 64 (4 * i)) 32 =
    original.gpr (savedReg i)

structure SavePost (original current : State) : Prop where
  gpr : current.gpr = original.gpr
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  sp : current.sp = original.sp
  saved : Saved original current
  frame : Frame [⟨State.addr (original.gpr .r2), 36⟩] original.mem current.mem

theorem blockSave_ok (s : State)
    (fit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (hw : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockSave) s (SavePost s) := by
  rw [blockSave_eq]
  obtain ⟨t, s', he, hs⟩ := VG.Proof.Rc2.Arm.saveCode_ok s .r2 savedReg 9 (by decide) fit hw
  refine ⟨t, s', he, hs.1, hs.2.1, hs.2.2.1, VG.Arm.Exec.sp he, ?_, ?_⟩
  · intro i hi
    rw [hs.1, hs.2.2.2]
    exact VG.Proof.Rc2.Arm.saveMem_read _ _ _ 9 (by decide) i hi
  · rw [hs.2.2.2]
    exact VG.Proof.Rc2.Arm.saveMem_frame _ _ _ 9 (by decide)

theorem savedReg_separate : ∀ i < 9, savedReg i ≠ .r2 := by decide +kernel

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ savedRegs, current.gpr r = original.gpr r
  keep : VG.Proof.Rc2.Arm.Keep savedRegs origin current
  sp : current.sp = origin.sp

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (fit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (hread : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockRestore) s (RestorePost original s) := by
  rw [blockRestore_eq]
  have hregs : (List.range 9).map savedReg = savedRegs := by decide +kernel
  obtain ⟨t, s', he, hs⟩ := VG.Proof.Rc2.Arm.restoreCode_ok s .r2 savedReg (List.range 9) original.gpr fit
    (fun i hi => by have := List.mem_range.mp hi; omega)
    (fun i hi => savedReg_separate i (List.mem_range.mp hi))
    (fun i hi => hread i (List.mem_range.mp hi))
    (fun i hi => hsaved i (List.mem_range.mp hi))
  rw [hregs] at hs
  exact ⟨t, s', he, hs.1, hs.2, VG.Arm.Exec.sp he⟩

theorem savedSlot_spill_disjoint (s : State) (i : Nat) (hi : i < 9) :
    (⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint (spillRegion s) :=
  Offset.disjoint (State.addr (s.gpr .r2)) (by omega) (by omega) (by decide)

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .r2 = s.gpr .r2) (hf : Frame [spillRegion s] s.mem t.mem) :
    Saved original t := by
  intro i hi
  have hmem := hf.readW (a := State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) (w := 32)
    (r := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i), 4⟩) (Region.contains_self _ _)
    (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact savedSlot_spill_disjoint s i hi)
    (by decide)
  rw [hbase]
  exact hmem.trans (hs i hi)

end VG.Proof.TripleDes.Arm

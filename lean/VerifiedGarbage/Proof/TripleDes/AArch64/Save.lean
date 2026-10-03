import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundStep

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

def savedReg (i : Nat) : Reg := savedRegs.getD i .x19

theorem blockSave_eq : blockSave = Spill.saveCode .x2 (Spill.slots savedReg 4) := by
  decide +kernel

theorem blockRestore_eq : blockRestore = Spill.restoreCode .x2 (Spill.slots savedReg 4) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 4, current.mem.readW (current.gpr .x2 + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

structure SavePost (original current : State) : Prop where
  gpr : current.gpr = original.gpr
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  sp : current.sp = original.sp
  saved : Saved original current
  frame : Frame [⟨original.gpr .x2, 32⟩] original.mem current.mem

theorem blockSave_ok (s : State)
    (hw : ∀ i < 4, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockSave) s (SavePost s) := by
  rw [blockSave_eq]
  refine WP.mono (Spill.save_wp (by decide) (Spill.forall_slots hw)) fun s' h =>
    ⟨h.gpr, h.rd, h.wr, h.sp, fun i hi => ?_, ?_⟩
  · rw [h.gpr, h.mem]
    exact Spill.saveMem_saved (l := Spill.slots savedReg 4) (by decide) s.mem (s.gpr .x2) s.gpr
      (savedReg i, 8 * i) (Spill.mem_slots hi)
  · rw [h.mem]; exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem savedReg_separate : ∀ i < 4, savedReg i ≠ .x2 := by decide +kernel

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ savedRegs, current.gpr r = original.gpr r
  keep : VG.Proof.Rc2.AArch64.Keep savedRegs origin current
  sp : current.sp = origin.sp

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockRestore) s (RestorePost original s) := by
  rw [blockRestore_eq]
  have hregs : (Spill.slots savedReg 4).map Prod.fst = savedRegs := by decide +kernel
  exact WP.mono (Spill.restore_wp rfl (by decide) (by decide) (Spill.forall_slots hread)
    (Spill.forall_slots hsaved)) fun s' h =>
    ⟨fun r hr => h.gpr_of (.inl (hregs ▸ hr)), ⟨fun r hr => h.other r (hregs ▸ hr), h.mem, h.rd, h.wr⟩,
      h.sp⟩

theorem savedSlot_spill_disjoint (s : State) (i : Nat) (hi : i < 4) :
    (⟨s.gpr .x2 + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (spillRegion s) :=
  Offset.disjoint (s.gpr .x2) (by omega) (by omega) (by decide)

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .x2 = s.gpr .x2) (hf : Frame [spillRegion s] s.mem t.mem) :
    Saved original t := by
  intro i hi
  have hmem := hf.readW (a := s.gpr .x2 + BitVec.ofNat 64 (8 * i)) (w := 64)
    (r := ⟨s.gpr .x2 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact savedSlot_spill_disjoint s i hi)
    (by decide)
  rw [hbase]
  exact hmem.trans (hs i hi)

end VG.Proof.TripleDes.AArch64

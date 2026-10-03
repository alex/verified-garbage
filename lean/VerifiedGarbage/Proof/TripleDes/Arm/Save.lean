import VerifiedGarbage.Proof.Rc2.Arm.Save
import VerifiedGarbage.Proof.TripleDes.Arm.RoundStep

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (slotsOf)

theorem blockSave_eq : blockSave = (slotsOf savedRegs).map (fun p => Instr.str p.1 .r2 p.2) := by
  rw [blockSave, slotsOf, List.map_map]; rfl

theorem blockRestore_eq : blockRestore = (slotsOf savedRegs).map (fun p => Instr.ldr p.1 .r2 p.2) := by
  rw [blockRestore, slotsOf, List.map_map]; rfl

theorem slots_ok : Spill.Slots 0 36 (slotsOf savedRegs) := by decide

theorem slot_index : ∀ p ∈ slotsOf savedRegs, ∃ i < 9, p.2 = 4 * i := by decide

def Saved (original current : State) : Prop :=
  Spill.Saved current.mem (State.addr (current.gpr .r2)) original.gpr (slotsOf savedRegs)

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
  rw [blockSave_eq, ← List.append_nil (List.map _ _)]
  refine Spill.save_ok _ s _ (fun p hp => ?_) (WP.block_nil ⟨rfl, rfl, rfl, rfl,
    Spill.saveMem_saved _ _ _ _ slots_ok, Spill.saveMem_frame _ _ _ (by decide) _ (by decide)⟩)
  obtain ⟨i, hi, he⟩ := slot_index p hp
  exact ⟨by omega, by omega, he ▸ hw i hi⟩

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ savedRegs, current.gpr r = original.gpr r
  keep : VG.Proof.Rc2.Arm.Keep savedRegs origin current
  sp : current.sp = origin.sp

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (fit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (hread : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockRestore) s (RestorePost original s) := by
  rw [blockRestore_eq, ← List.append_nil (List.map _ _)]
  have hregs : (slotsOf savedRegs).map Prod.fst = savedRegs := by decide
  refine Spill.restoreList_ok _ s _ (by decide) (fun p hp => ?_)
    fun s' hl ho hm hrd hwr hsp => WP.block_nil ⟨?_, ⟨fun r hr => ho r (hregs ▸ hr), hm, hrd, hwr⟩, hsp⟩
  · obtain ⟨i, hi, he⟩ := slot_index p hp
    have hne : ∀ p ∈ slotsOf savedRegs, p.1 ≠ .r2 := by decide
    exact ⟨hne p hp, by omega, by omega, he ▸ hread i hi⟩
  · exact Spill.restored_of (hsaved.restored hl) fun r hr => hregs ▸ hr

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .r2 = s.gpr .r2) (hf : Frame [spillRegion s] s.mem t.mem) :
    Saved original t := by
  unfold Saved; rw [hbase]
  exact Spill.Saved.frame hs slots_ok hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

end VG.Proof.TripleDes.Arm

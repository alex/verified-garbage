import VerifiedGarbage.Proof.Rc2.Arm.Save
import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (slotsOf)

theorem save_eq : Impl.TripleDes.Arm.Key.save =
    (slotsOf Impl.TripleDes.Arm.Key.savedRegs).map (fun p => Instr.str p.1 .r3 p.2) := by
  rw [Impl.TripleDes.Arm.Key.save, slotsOf, List.map_map]; rfl

theorem restore_eq : Impl.TripleDes.Arm.Key.restore =
    (slotsOf Impl.TripleDes.Arm.Key.savedRegs).map (fun p => Instr.ldr p.1 .r3 p.2) := by
  rw [Impl.TripleDes.Arm.Key.restore, slotsOf, List.map_map]; rfl

theorem slots_ok : Spill.Slots 0 36 (slotsOf Impl.TripleDes.Arm.Key.savedRegs) := by decide

theorem slot_index : ∀ p ∈ slotsOf Impl.TripleDes.Arm.Key.savedRegs, ∃ i < 9, p.2 = 4 * i := by decide

def Saved (original current : State) : Prop :=
  Spill.Saved current.mem (State.addr (current.gpr .r3)) original.gpr (slotsOf Impl.TripleDes.Arm.Key.savedRegs)

theorem save_ok (s : State)
    (fit : (s.gpr .r3).toNat + 256 ≤ 2 ^ 32)
    (hw : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block Impl.TripleDes.Arm.Key.save) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Saved s s' ∧
      Frame [⟨State.addr (s.gpr .r3), 36⟩] s.mem s'.mem) := by
  rw [save_eq, ← List.append_nil (List.map _ _)]
  refine Spill.save_ok _ s _ (fun p hp => ?_) (WP.block_nil ⟨rfl, rfl, rfl,
    Spill.saveMem_saved _ _ _ _ slots_ok, Spill.saveMem_frame _ _ _ (by decide) _ (by decide)⟩)
  obtain ⟨i, hi, he⟩ := slot_index p hp
  exact ⟨by omega, by omega, he ▸ hw i hi⟩

theorem restore_ok (original s : State) (hsaved : Saved original s)
    (fit : (s.gpr .r3).toNat + 256 ≤ 2 ^ 32)
    (hread : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r3) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block Impl.TripleDes.Arm.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.Arm.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.Arm.Keep (Impl.TripleDes.Arm.Key.savedRegs) s s') := by
  rw [restore_eq, ← List.append_nil (List.map _ _)]
  have hregs : (slotsOf Impl.TripleDes.Arm.Key.savedRegs).map Prod.fst = Impl.TripleDes.Arm.Key.savedRegs := by
    decide
  refine Spill.restoreList_ok _ s _ (by decide) (fun p hp => ?_)
    fun s' hl ho hm hrd hwr _ => WP.block_nil ⟨?_, ⟨fun r hr => ho r (hregs ▸ hr), hm, hrd, hwr⟩⟩
  · obtain ⟨i, hi, he⟩ := slot_index p hp
    have hne : ∀ p ∈ slotsOf Impl.TripleDes.Arm.Key.savedRegs, p.1 ≠ .r3 := by decide
    exact ⟨hne p hp, by omega, by omega, he ▸ hread i hi⟩
  · exact Spill.restored_of (hsaved.restored hl) fun r hr => hregs ▸ hr

end VG.Proof.TripleDes.Arm.Key

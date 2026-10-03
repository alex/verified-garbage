import VerifiedGarbage.Proof.CmacTripleDes.Arm.Contract
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Block
import VerifiedGarbage.Proof.MdStream.Arm.Common

/-!
# TDEA-CMAC on ARMv7: saving and restoring the registers

Untrusted: everything here is checked by Lean. Each function saves our
caller's callee-saved registers to bytes `[52, 88)` of the scratch buffer
(`save`), and restores them from there through `r10`, `r10` last
(`restore`).
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm
open VG.Proof.MdStream.Arm (saveMem)

theorem saved_bound : ∀ p ∈ saved, 52 ≤ p.2 ∧ p.2 + 4 ≤ 88 := by decide

/-- The memory after saving the registers to the scratch buffer at `S`. -/
def savedMem (s₀ : State) (S : BitVec 32) : Mem := saveMem s₀.mem (State.addr S) s₀.gpr saved

export VG.Arm.Spill (saveMem_congr)

theorem saved_slots : Spill.Slots 52 88 saved := by decide

theorem savedMem_frame (s₀ : State) (S : BitVec 32) :
    Frame [⟨State.addr S + BitVec.ofNat 64 52, 36⟩] s₀.mem (savedMem s₀ S) :=
  Spill.saveMem_frame_slots saved_slots _ _ _

/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (savedMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (State.addr S) s₀.gpr s₀.mem saved saved_slots (r, d) h

/-- The registers but `r10`, and where they are saved. -/
def saved8 : List (Reg × Nat) :=
  [(.r4, 52), (.r5, 56), (.r6, 60), (.r7, 64), (.r8, 68), (.r9, 72), (.r11, 76), (.lr, 80)]

theorem saved_eq : saved = saved8 ++ [(.r10, 84)] := rfl

/-- `restore` from the scratch buffer at `S`: each register gets its slot. -/
theorem restore_ok {s : State} {S : BitVec 32} (hb : s.gpr .r10 = S) (hS : S.toNat + 88 ≤ 2 ^ 32)
    (hr : ∀ d, 52 ≤ d → d + 4 ≤ 88 → InRegions (s.rd ++ s.wr) (State.addr S + BitVec.ofNat 64 d) 4) :
    WP isa (.block restore) s fun s' =>
      (∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (State.addr S + BitVec.ofNat 64 p.2) 32) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [restore, saved_eq, ← List.append_nil (List.map _ _)]
  subst hb
  refine Spill.restoreBase_ok (by decide) (fun p hp => ?_) fun s' hl _ hm hrd hwr hsp => WP.block_nil ⟨hl, hsp, hm, hrd, hwr⟩
  have := saved_slots.bound hp
  exact ⟨by omega, by omega, hr _ this.1 this.2.1⟩

/-- The registers restored from slots that have not changed since they were
saved. -/
theorem restored {s₀ s s' : State} {S : BitVec 32}
    (hm : ∀ d, 52 ≤ d → d + 4 ≤ 88 →
      s.mem.readW (State.addr S + BitVec.ofNat 64 d) 32 = (savedMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32)
    (h : ∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (State.addr S + BitVec.ofNat 64 p.2) 32) (hsp : s'.sp = s₀.sp) :
    abiPreserved s₀ s' := by
  refine ⟨fun r hr => ?_, hsp⟩
  have hk : ∀ r ∈ preserved, r ∈ saved.map Prod.fst := by decide
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hk r hr)
  have hb := saved_bound _ hp
  rw [h _ hp, hm p.2 hb.1 hb.2, savedMem_slot s₀ S hp]

end VG.Proof.CmacTripleDes.Arm

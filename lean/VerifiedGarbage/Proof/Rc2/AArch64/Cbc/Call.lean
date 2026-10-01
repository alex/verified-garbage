import VerifiedGarbage.Proof.Rc2.AArch64.Block
import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Calling the verified block primitive from CBC -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def savedAcrossCall : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

def kept : List Reg := [.x0, .x1, .x2, .x23, .x24]

theorem block_keeps (d : Spec.Rc2.Direction) :
    ((instrs (.block (blockCode d) : Prog isa)).all fun i => kept.all fun r => decide (dstOf i ≠ some r)) = true := by
  cases d
  · change ((instrs encryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide
  · change ((instrs decryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide

theorem block_keeps_reg (d : Spec.Rc2.Direction) {r : Reg} (hr : r ∈ kept) :
    ∀ i ∈ instrs (.block (blockCode d) : Prog isa), dstOf i ≠ some r := by
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (block_keeps d) i hi) r hr
  simpa using h

theorem block_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    ∃ t s', Exec isa (.block (blockCode d)) s t s' ∧ abiPreserved s s' ∧ (blockContract d).post s s' := by
  cases d
  · exact encrypt_correct s hs
  · exact decrypt_correct s hs

theorem blockCall_eq (d : Spec.Rc2.Direction) : Impl.Rc2.AArch64.Cbc.blockCall d =
    .call (match d with | .encrypt => "vg_rc2_encrypt_block" | .decrypt => "vg_rc2_decrypt_block")
      (.block (blockCode d)) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨s.gpr .x0, 128⟩, ⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] (s.rd ++ s.wr)
  writes : Covers [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] s.wr
  keyScratch : (Region.mk (s.gpr .x0) 128).Disjoint ⟨s.gpr .x2, 256⟩
  dataScratch : (Region.mk (s.gpr .x1) 8).Disjoint ⟨s.gpr .x2, 256⟩

structure CallPost (d : Spec.Rc2.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] s.mem s'.mem
  output : Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))

theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  refine WP.call (k := blockContract d) (block_correct' d)
    (rd := [⟨s.gpr .x0, 128⟩]) (wr := [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩]) ?_ hp.reads hp.writes ?_ (by rfl)
  · simp only [blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch⟩
  · intro s' rd wr sp frame callee regs out
    have sep : ∀ r ∈ kept, r ∉ linkRegs := by decide
    have saved : ∀ r ∈ savedAcrossCall, r ∈ preserved ∧ r ≠ .x30 := by decide
    refine ⟨fun r hr => regs r (sep r hr) (block_keeps_reg d hr),
      fun r hr => callee r (saved r hr).1 (saved r hr).2, rd, wr, frame, ?_⟩
    change Spec.Rc2.blockAt s'.mem _ = cipher d _ _ at out
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs)] at out
    exact out

end VG.Proof.Rc2.AArch64.Cbc

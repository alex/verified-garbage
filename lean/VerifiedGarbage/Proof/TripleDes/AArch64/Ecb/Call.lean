import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
import VerifiedGarbage.Impl.TripleDes.AArch64.Ecb
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Calling the verified block primitive from ECB -/

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

def savedAcrossCall : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

def kept : List Reg := [.x0, .x1, .x2, .x23, .x24]

theorem block_keeps (d : Spec.TripleDes.Direction) :
    ((instrs (block d)).all fun i => kept.all fun r => decide (dstOf i ≠ some r)) = true := by
  cases d
  · change ((instrs encryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide
  · change ((instrs decryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide

theorem block_keeps_reg (d : Spec.TripleDes.Direction) {r : Reg} (hr : r ∈ kept) :
    ∀ i ∈ instrs (block d), dstOf i ≠ some r := by
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (block_keeps d) i hi) r hr
  simpa using h

theorem block_correct' (d : Spec.TripleDes.Direction) (s : State) (hs : (blockContract d).pre s) :
    ∃ t s', Exec isa (block d) s t s' ∧ abiPreserved s s' ∧ (blockContract d).post s s' := by
  cases d
  · exact encrypt_correct s hs
  · exact decrypt_correct s hs

theorem blockCall_eq (d : Spec.TripleDes.Direction) : Impl.TripleDes.AArch64.Ecb.blockCall d =
    .call (match d with | .encrypt => "vg_triple_des_encrypt_block" | .decrypt => "vg_triple_des_decrypt_block")
      (block d) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨s.gpr .x0, 384⟩, ⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 512⟩] s.wr
  keyScratch : (Region.mk (s.gpr .x0) 384).Disjoint ⟨s.gpr .x2, 512⟩
  dataScratch : (Region.mk (s.gpr .x1) 8).Disjoint ⟨s.gpr .x2, 512⟩

structure CallPost (d : Spec.TripleDes.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 512⟩] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (s.gpr .x1) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d (Spec.TripleDes.blockAt s.mem (s.gpr .x1))

theorem call_ok (d : Spec.TripleDes.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.TripleDes.AArch64.Ecb.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  refine WP.call (k := blockContract d) (block_correct' d)
    (rd := [⟨s.gpr .x0, 384⟩]) (wr := [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 512⟩]) ?_ hp.reads hp.writes ?_ (by cases d <;> rfl)
  · simp only [blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch⟩
  · intro s' rd wr sp frame callee regs out
    have sep : ∀ r ∈ kept, r ∉ linkRegs := by decide
    have saved : ∀ r ∈ savedAcrossCall, r ∈ preserved ∧ r ≠ .x30 := by decide
    refine ⟨fun r hr => regs r (sep r hr) (block_keeps_reg d hr),
      fun r hr => callee r (saved r hr).1 (saved r hr).2, rd, wr, frame, ?_⟩
    change Spec.TripleDes.blockAt s'.mem _ = blockResult _ d _ at out
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs)] at out
    exact out

end VG.Proof.TripleDes.AArch64.Ecb

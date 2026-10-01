import VerifiedGarbage.Proof.Rc2.Arm.Block
import VerifiedGarbage.Impl.Rc2.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.Call

/-! # Calling the verified block primitive from CBC -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

def savedAcrossCall : List Reg := [.r8, .r9, .r10, .r11]

def args : List Reg := [.r0, .r1, .r2]

def kept : List Reg := [.r0, .r1, .r2, .r4, .r5]

theorem block_keeps (d : Spec.Rc2.Direction) :
    ((instrs (.block (blockCode d) : Prog isa)).all fun i => args.all fun r => decide (dstOf i ≠ some r)) = true := by
  cases d
  · change ((instrs encryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide
  · change ((instrs decryptBlock).all _) = true
    rw [← Code.allInstrs_eq]; lit_decide

theorem block_keeps_reg (d : Spec.Rc2.Direction) {r : Reg} (hr : r ∈ args) :
    ∀ i ∈ instrs (.block (blockCode d) : Prog isa), dstOf i ≠ some r := by
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (block_keeps d) i hi) r hr
  simpa using h

theorem block_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (blockContract d).pre s) :
    ∃ t s', Exec isa (.block (blockCode d)) s t s' ∧ abiPreserved s s' ∧ (blockContract d).post s s' := by
  cases d
  · exact encrypt_correct s hs
  · exact decrypt_correct s hs

theorem blockCall_eq (d : Spec.Rc2.Direction) : Impl.Rc2.Arm.Cbc.blockCall d =
    .call (match d with | .encrypt => "vg_rc2_encrypt_block" | .decrypt => "vg_rc2_decrypt_block")
      (.block (blockCode d)) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨State.addr (s.gpr .r0), 128⟩, ⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩] s.wr
  keyScratch : (Region.mk (State.addr (s.gpr .r0)) 128).Disjoint ⟨State.addr (s.gpr .r2), 256⟩
  keyFit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32
  bufFit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32
  dataScratch : (Region.mk (State.addr (s.gpr .r1)) 8).Disjoint ⟨State.addr (s.gpr .r2), 256⟩

structure CallPost (d : Spec.Rc2.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩] s.mem s'.mem
  output : Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) =
    cipher d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))

theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  refine WP.call (k := blockContract d) (block_correct' d)
    (rd := [⟨State.addr (s.gpr .r0), 128⟩]) (wr := [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 256⟩]) ?_ hp.reads hp.writes ?_ (by rfl)
  · simp only [blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.keyFit, hp.dataFit, hp.bufFit⟩
  · intro s' rd wr sp frame callee regs out
    have sep : ∀ r ∈ kept, r ∉ linkRegs := by decide
    have saved : ∀ r ∈ savedAcrossCall, r ∈ preserved ∧ r ≠ .lr := by decide
    refine ⟨fun r hr => ?_,
      fun r hr => callee r (saved r hr).1 (saved r hr).2, rd, wr, frame, ?_⟩
    · by_cases ha : r ∈ args
      · exact regs r (block_keeps_reg d ha) (sep r hr)
      · have saved : ∀ r ∈ kept, r ∉ args → r ∈ preserved ∧ r ≠ .lr := by decide
        exact callee r (saved r hr ha).1 (saved r hr ha).2
    · change Spec.Rc2.blockAt s'.mem _ = cipher d _ _ at out
      simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs)] at out
      exact out

end VG.Proof.Rc2.Arm.Cbc

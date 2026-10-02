import VerifiedGarbage.Impl.Argon2.AArch64.FillLanes
import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetup

/-! Lane advancement retains the allocation and public segment parameters. -/

namespace VG.Proof.Argon2.AArch64.FillLanes

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillLanes

theorem advance_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8)
    (ha : (s.gpr .x24 + 1).toNat < 2 ^ 63)
    (hb : (s.mem.readW (off (s.gpr .x19) 184) 64).toNat < 2 ^ 63) :
    WP isa (.block advance) s fun t => t.gpr .x24 = s.gpr .x24 + 1 ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x24 + 1).toNat <
        (s.mem.readW (off (s.gpr .x19) 184) 64).toNat)) ∧
      Divide.Keeps [.x24, .x12, .x13, .x14, .x15] s t := by
  simp only [advance, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.addi_ok s .x24 1 (by decide) (by decide) (by decide)).mono ?_
  rintro u ⟨value, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have read : InRegions (u.rd ++ u.wr) (off (u.gpr .x19) 184) 8 := by
    rw [keeps.rd, keeps.wr, bp]; exact hr
  have left : (u.gpr .x24).toNat < 2 ^ 63 := by rw [value]; exact ha
  have right : (u.mem.readW (off (u.gpr .x19) 184) 64).toNat < 2 ^ 63 := by
    rw [keeps.mem, bp]; exact hb
  refine (Instructions.comparem_ok u .x24 .x19 184 (by decide) (by decide) (by decide)
    read left right).mono ?_
  rintro t ⟨flag, changed⟩
  refine ⟨(changed.regs .x24 (by decide)).trans value, ?_,
    (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
  rw [flag, value, keeps.mem, bp]
  rfl

theorem context_ready {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : FillContext.Ready p pass lane slice index old s) : SegmentSetup.Ready p pass lane slice s :=
  ⟨h.parameters, h.layout, h.cache.layout, h.cache.reads, h.cache.write, ⟨old, h.cache.words⟩,
    h.matrixWork, h.position.laneLength, h.position.segmentLength, h.lanesWord⟩

theorem finished_ready {p : Params} {pass lane slice : Nat} {s t : State} {state : FillState}
    (parameters : FillContext.Parameters p pass lane slice) (h : FillSegment.Finished s t p pass lane slice state) :
    SegmentSetup.Ready p pass lane slice t := by
  obtain ⟨old, context⟩ := FillContext.finished_context parameters h
  exact context_ready context

theorem change_lane_ready {p : Params} {pass lane slice newLane : Nat} {s t : State}
    (h : SegmentSetup.Ready p pass lane slice s) (k : Divide.Keeps [.x24, .x12, .x13, .x14, .x15] s t)
    (value : t.gpr .x24 = BitVec.ofNat 64 newLane) (active : newLane < p.lanes) :
    SegmentSetup.Ready p pass newLane slice t := by
  have bp := k.regs .x19 (by decide)
  have sp := k.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨{ h.parameters with laneBound := active }, h.layout.of_preserved bp sp base work k.rd k.wr,
    ?_, ?_, ?_, ?_, ?_, (k.regs .x20 (by decide)).trans h.laneLength,
    (k.regs .x21 (by decide)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [k.rd, k.wr, bp]; exact h.addressLayout.frameRead
    · rw [k.wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [k.rd, k.wr, bp]; exact h.reads
  · rw [k.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, value, (k.regs .x22 (by decide)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [k.mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

end VG.Proof.Argon2.AArch64.FillLanes

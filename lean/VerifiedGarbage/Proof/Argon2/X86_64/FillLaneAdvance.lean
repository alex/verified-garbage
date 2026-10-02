import VerifiedGarbage.Impl.Argon2.X86_64.FillLanes
import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetup

/-! Lane advancement retains the allocation and public segment parameters. -/

namespace VG.Proof.Argon2.X86_64.FillLanes

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillLanes

theorem advance_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8) :
    WP isa (.block advance) s fun t => t.gpr .rbx = s.gpr .rbx + 1 ∧
      t.cf = decide ((s.gpr .rbx + 1).toNat < (s.mem.readW (off (s.gpr .rbp) 184) 64).toNat) ∧
      Divide.Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags, hr,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    reduceCtorEq, ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

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
    (h : SegmentSetup.Ready p pass lane slice s) (k : Divide.Keeps [.rbx] s t)
    (value : t.gpr .rbx = BitVec.ofNat 64 newLane) (active : newLane < p.lanes) :
    SegmentSetup.Ready p pass newLane slice t := by
  have bp := k.regs .rbp (by decide)
  have sp := k.regs .rsp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨{ h.parameters with laneBound := active }, h.layout.of_preserved bp sp base work k.rd k.wr,
    ?_, ?_, ?_, ?_, ?_, (k.regs .r12 (by decide)).trans h.laneLength,
    (k.regs .r13 (by decide)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [k.rd, k.wr, bp]; exact h.addressLayout.frameRead
    · rw [k.wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [k.rd, k.wr, bp]; exact h.reads
  · rw [k.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, value, (k.regs .r14 (by decide)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [k.mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

end VG.Proof.Argon2.X86_64.FillLanes

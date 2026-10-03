import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelSpec
import VerifiedGarbage.Impl.Argon2.AArch64.DependentWord
import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelArgs
import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelPrepare

/-! Merged from `Proof.Argon2.AArch64.DependentWordPointer`. -/
section
/-! The data-dependent word's address is the specification's cyclic predecessor. -/

namespace VG.Proof.Argon2.AArch64.DependentWord

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

theorem args_ok (s : State) : WP isa (.block args) s fun t =>
    t.gpr .x3 = s.gpr .x0 ∧ t.gpr .x8 = s.gpr .x24 ∧ Divide.Keeps [.x3, .x8] s t := by
  apply WP.of_runBlock
  simp only [args, Impl.Argon2.AArch64.Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem pointer_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa pointer s fun t =>
      t.gpr .x8 = FillKernel.previous s p lane slice index ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold pointer Impl.Argon2.AArch64.FillKernel.matrix
  refine WP.seq ((FillKernel.load_ok s .x4 232 (by decide) (by decide) (h.layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, ka⟩
  have k : Divide.Keeps ReferenceMap.changed s a := ka.mono (by decide)
  have pos := h.position.of_keeps k
  have columnBound := Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound
  have segment := Proof.Argon2.segmentLen_ge_two p h.bounds.lanesPositive h.bounds.memoryMinimum
  have q := Proof.Argon2.laneLen_segments p h.bounds.lanesPositive
  refine WP.seq ((FillColumn.code_nat_ok a slice p.segmentLen index p.laneLen
    pos.slice pos.segmentLength pos.index pos.laneLength (by omega)
    (Nat.lt_trans h.bounds.laneLength_bound (by decide)) columnBound).mono ?_)
  rintro b ⟨_, prev, kb⟩
  refine WP.seq ((args_ok b).mono ?_)
  rintro c ⟨col, laneReg, kc⟩
  have col' := col.trans prev
  have lane' : c.gpr .x8 = BitVec.ofNat 64 lane := laneReg.trans ((kb.regs .x24 (by decide)).trans pos.current)
  have length : c.gpr .x20 = BitVec.ofNat 64 p.laneLen :=
    (kc.regs .x20 (by decide)).trans ((kb.regs .x20 (by decide)).trans pos.laneLength)
  refine (BlockAddress.code_nat_ok c lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) p.laneLen lane' col' length).mono ?_
  rintro t ⟨address, kt⟩
  refine ⟨?_, ((k.trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [address, kc.regs .x4 (by decide), kb.regs .x4 (by decide), base]
  rfl

end VG.Proof.Argon2.AArch64.DependentWord
end

/-! Select the specified secret random word from the public previous-cell address. -/

namespace VG.Proof.Argon2.AArch64.DependentWord

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.DependentWord

theorem read_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .x8) 8) :
    WP isa (.block Impl.Argon2.AArch64.DependentWord.read) s fun t => t.gpr .x0 = s.mem.readW (s.gpr .x8) 64 ∧ Divide.Keeps [.x0] s t := by
  simpa only [Impl.Argon2.AArch64.DependentWord.read,
    List.flatten_cons, List.flatten_nil, List.append_nil, BitVec.add_zero]
    using Instructions.load_ok s .x0 .x8 0 (by decide) (by decide)
      (by simpa only [BitVec.add_zero] using hr)

theorem code_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa code s fun t =>
      t.gpr .x0 = (blockAt s.mem (FillKernel.previous s p lane slice index))[0] ∧
      Divide.Keeps ReferenceMap.changed s t := by
  unfold code
  refine WP.seq ((pointer_ok s p pass lane slice index h).mono ?_)
  rintro a ⟨pointer, keeps⟩
  have bound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  have cover := h.layout.cell_cover h.bounds.lanesPositive h.bounds.laneBound bound
  have hr : InRegions (a.rd ++ a.wr) (a.gpr .x8) 8 := by
    rw [keeps.rd, keeps.wr, pointer]
    have contains : (⟨FillKernel.previous s p lane slice index, 1024⟩ : Region).Contains
        (FillKernel.previous s p lane slice index) 8 :=
      by simpa only [BitVec.add_zero] using (Offset.contains_base
        (FillKernel.previous s p lane slice index) (d := 0) (n := 8) (k := 1024) (by decide) (by decide))
    obtain ⟨r, hr, hc⟩ := cover _ _ ⟨⟨FillKernel.previous s p lane slice index, 1024⟩,
      by simp [FillKernel.previous, FillKernel.previousColumn, FillKernel.currentColumn], contains⟩
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (read_ok a hr).mono ?_
  rintro t ⟨random, tail⟩
  refine ⟨?_, keeps.trans (tail.mono (by decide))⟩
  rw [random, pointer, keeps.mem]
  change s.mem.readW _ 64 = (blockAt _ _)[(⟨0, by decide⟩ : Fin 128)]
  rw [blockAt_get]
  change s.mem.readW _ 64 = s.mem.readW (_ + 0#64) 64
  rw [BitVec.add_zero]

theorem code_spec_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (dependent : independent p pass slice = false) : WP isa code s fun t =>
      t.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
      Divide.Keeps ReferenceMap.changed s t := by
  refine (code_ok s p pass lane slice index h).mono ?_
  rintro t ⟨random, keeps⟩
  have bound := Proof.Argon2.previous_cell_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    h.bounds.laneBound (column := FillKernel.currentColumn p slice index)
  have block := represented.block (FillKernel.previousIndex p lane slice index) bound
  change blockAt s.mem (FillKernel.previous s p lane slice index) = _ at block
  rw [block] at random
  refine ⟨?_, keeps⟩
  simpa only [Proof.Argon2.FillStep.random, dependent, Bool.false_eq_true, ite_false, FillKernel.previousIndex, FillKernel.previousColumn,
    FillKernel.currentColumn] using random

end VG.Proof.Argon2.AArch64.DependentWord

import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelSpec
import VerifiedGarbage.Impl.Argon2.X86_64.DependentWord
import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelArgs
import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelPrepare

/-! Merged from `Proof.Argon2.X86_64.DependentWordPointer`. -/
section
/-! The data-dependent word's address is the specification's cyclic predecessor. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

theorem args_ok (s : State) : WP isa (.block args) s fun t =>
    t.gpr .rcx = s.gpr .rdi ∧ t.gpr .rax = s.gpr .rbx ∧ Divide.Keeps [.rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

theorem pointer_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa pointer s fun t =>
      t.gpr .rax = FillKernel.previous s p lane slice index ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold pointer
  refine WP.seq ((FillKernel.load_ok s .r8 232 (h.layout.frameRead 232 (by simp))).mono ?_)
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
  have lane' : c.gpr .rax = BitVec.ofNat 64 lane := laneReg.trans ((kb.regs .rbx (by decide)).trans pos.current)
  have length : c.gpr .r12 = BitVec.ofNat 64 p.laneLen :=
    (kc.regs .r12 (by decide)).trans ((kb.regs .r12 (by decide)).trans pos.laneLength)
  refine (BlockAddress.code_nat_ok c lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) p.laneLen lane' col' length).mono ?_
  rintro t ⟨address, kt⟩
  refine ⟨?_, ((k.trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [address, kc.regs .r8 (by decide), kb.regs .r8 (by decide), base]
  rfl

end VG.Proof.Argon2.X86_64.DependentWord
end

/-! Select the specified secret random word from the public previous-cell address. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

theorem read_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rax) 8) :
    WP isa (.block Impl.Argon2.X86_64.DependentWord.read) s fun t => t.gpr .rdi = s.mem.readW (s.gpr .rax) 64 ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.DependentWord.read, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, BitVec.add_zero, hr, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa code s fun t =>
      t.gpr .rdi = (blockAt s.mem (FillKernel.previous s p lane slice index))[0] ∧
      Divide.Keeps ReferenceMap.changed s t := by
  unfold code
  refine WP.seq ((pointer_ok s p pass lane slice index h).mono ?_)
  rintro a ⟨pointer, keeps⟩
  have bound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  have cover := h.layout.cell_cover h.bounds.lanesPositive h.bounds.laneBound bound
  have hr : InRegions (a.rd ++ a.wr) (a.gpr .rax) 8 := by
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
      t.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
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

end VG.Proof.Argon2.X86_64.DependentWord

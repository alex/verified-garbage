import VerifiedGarbage.Proof.Argon2.AArch64.FillSegmentBody
import VerifiedGarbage.Proof.Argon2.AArch64.FillBlockCT
import VerifiedGarbage.Proof.Argon2.AArch64.FillBlockCounter

/-! Public counters and coordinates remain related across a segment iteration. -/

namespace VG.Proof.Argon2.AArch64.FillSegment

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillSegment

theorem advance_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x21, .x23], s.gpr r = t.gpr r)
    (.block advance) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x21, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

structure NextRelated (p : Params) (pass lane slice index : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : ∃ old, RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (FillBlock.Related p pass lane slice index old leftState rightState) body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (index + 1 < p.segmentLen →
        NextRelated p pass lane slice (index + 1)
          (fillBlock p pass slice lane index leftState) (fillBlock p pass slice lane index rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq fillA advanceA =>
    cases eb with
    | seq fillB advanceB =>
      obtain ⟨filledTrace, filledSp⟩ := FillBlock.code_rel p pass lane slice index old leftState rightState
        _ _ _ _ _ _ hp fillA fillB
      obtain ⟨_, sa, runA, filledA⟩ := FillBlock.code_ok s p pass lane slice index old hp.source.left leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := FillBlock.code_ok t p pass lane slice index old hp.source.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det fillA runA
      obtain ⟨_, rfl⟩ := Exec.det fillB runB
      obtain ⟨counterA, readyA⟩ := filledA.ready
      obtain ⟨counterB, readyB⟩ := filledB.ready
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ (by
        refine ⟨filledSp, ?_⟩
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact readyA.filling.position.segmentLength.trans readyB.filling.position.segmentLength.symm
        · exact readyA.filling.position.index.trans readyB.filling.position.index.symm) advanceA advanceB
      obtain ⟨_, a', advanceRunA, valueA, flagA, keptA⟩ := advance_nat_ok _ p pass lane slice index readyA.filling
      obtain ⟨_, b', advanceRunB, valueB, flagB, keptB⟩ := advance_nat_ok _ p pass lane slice index readyB.filling
      obtain ⟨_, rfl⟩ := Exec.det advanceA advanceRunA
      obtain ⟨_, rfl⟩ := Exec.det advanceB advanceRunB
      refine ⟨by rw [filledTrace, advancedTrace], flagA.trans flagB.symm, ?_⟩
      intro active
      have nextA := next_ready readyA keptA valueA active
      have nextB := next_ready readyB keptB valueB active
      have counterWordA := FillBlock.counter_run hp.source.left leftState hp.leftMatrix fillA
      have counterWordB := FillBlock.counter_run hp.source.right rightState hp.rightMatrix fillB
      have wordEq : BitVec.ofNat 64 counterA = BitVec.ofNat 64 counterB :=
        readyA.cache.words.counterWord.symm.trans
          (counterWordA.trans (counterWordB.symm.trans readyB.cache.words.counterWord))
      have counters := (ReferenceMap.word_eq counterA counterB readyA.cache.bound readyB.cache.bound).mp wordEq
      subst counterB
      refine ⟨⟨counterA, nextA, nextB, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [keptA.regs .x19 (by decide), keptB.regs .x19 (by decide),
          filledA.regs .x19 (by simp [FillCompress.loopRegs]), filledB.regs .x19 (by simp [FillCompress.loopRegs])]
        exact hp.source.bases
      · rw [keptA.sp, keptB.sp, filledA.sp, filledB.sp]
        exact hp.source.stacks
      · unfold FillKernel.matrix
        rw [keptA.mem, keptB.mem, keptA.regs .x19 (by decide), keptB.regs .x19 (by decide)]
        exact filledA.matrix.trans (hp.source.matrices.trans filledB.matrix.symm)
      · unfold AddressCalls.work
        rw [keptA.mem, keptB.mem, keptA.regs .x19 (by decide), keptB.regs .x19 (by decide)]
        exact filledA.work.trans (hp.source.work.trans filledB.work.symm)
      · unfold FillKernel.matrix
        rw [keptA.mem, keptA.regs .x19 (by decide)]
        exact filledA.represented
      · unfold FillKernel.matrix
        rw [keptB.mem, keptB.regs .x19 (by decide)]
        exact filledB.represented

end VG.Proof.Argon2.AArch64.FillSegment

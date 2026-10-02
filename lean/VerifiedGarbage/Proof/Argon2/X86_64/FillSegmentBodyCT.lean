import VerifiedGarbage.Proof.Argon2.X86_64.FillSegmentBody
import VerifiedGarbage.Proof.Argon2.X86_64.FillBlockCT
import VerifiedGarbage.Proof.Argon2.X86_64.FillBlockCounter

/-! Public counters and coordinates remain related across a segment iteration. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSegment

theorem advance_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r13, .r15], s.gpr r = t.gpr r)
    (.block advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r13, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

structure NextRelated (p : Params) (pass lane slice index : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : ∃ old, RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory

theorem body_rel (p : Params) (pass lane slice index old : Nat) (leftState rightState : FillState) :
    RelCT isa (FillBlock.Related p pass lane slice index old leftState rightState) body
      (fun s t => s.cf = t.cf ∧ (index + 1 < p.segmentLen →
        NextRelated p pass lane slice (index + 1)
          (fillBlock p pass slice lane index leftState) (fillBlock p pass slice lane index rightState) s t)) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq fillA advanceA =>
    cases eb with
    | seq fillB advanceB =>
      obtain ⟨filledTrace, _⟩ := FillBlock.code_rel p pass lane slice index old leftState rightState
        _ _ _ _ _ _ hp fillA fillB
      obtain ⟨_, sa, runA, filledA⟩ := FillBlock.code_ok s p pass lane slice index old hp.source.left leftState hp.leftMatrix
      obtain ⟨_, sb, runB, filledB⟩ := FillBlock.code_ok t p pass lane slice index old hp.source.right rightState hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det fillA runA
      obtain ⟨_, rfl⟩ := Exec.det fillB runB
      obtain ⟨counterA, readyA⟩ := filledA.ready
      obtain ⟨counterB, readyB⟩ := filledB.ready
      obtain ⟨advancedTrace, _⟩ := advance_rel _ _ _ _ _ _ (by
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
      · rw [keptA.regs .rbp (by decide), keptB.regs .rbp (by decide),
          filledA.regs .rbp (by simp [calleeSaved]), filledB.regs .rbp (by simp [calleeSaved])]
        exact hp.source.bases
      · rw [keptA.regs .rsp (by decide), keptB.regs .rsp (by decide),
          filledA.regs .rsp (by simp [calleeSaved]), filledB.regs .rsp (by simp [calleeSaved])]
        exact hp.source.stacks
      · unfold FillKernel.matrix
        rw [keptA.mem, keptB.mem, keptA.regs .rbp (by decide), keptB.regs .rbp (by decide)]
        exact filledA.matrix.trans (hp.source.matrices.trans filledB.matrix.symm)
      · unfold AddressCalls.work
        rw [keptA.mem, keptB.mem, keptA.regs .rbp (by decide), keptB.regs .rbp (by decide)]
        exact filledA.work.trans (hp.source.work.trans filledB.work.symm)
      · unfold FillKernel.matrix
        rw [keptA.mem, keptA.regs .rbp (by decide)]
        exact filledA.represented
      · unfold FillKernel.matrix
        rw [keptB.mem, keptB.regs .rbp (by decide)]
        exact filledB.represented

end VG.Proof.Argon2.X86_64.FillSegment

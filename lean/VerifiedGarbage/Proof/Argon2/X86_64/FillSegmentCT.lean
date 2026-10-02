import VerifiedGarbage.Proof.Argon2.X86_64.FillSegment
import VerifiedGarbage.Proof.Argon2.X86_64.FillSegmentBodyCT
import VerifiedGarbage.Proof.Argon2.SegmentIndices

/-! The segment loop exposes only the reviewed segment reference log. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass lane slice index count old : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  source : RandomSource.Related p pass lane slice index old s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice index count leftState).indices =
    (Proof.Argon2.segment p pass lane slice index count rightState).indices

theorem loop_rel (p : Params) (pass lane slice index count old : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endIndex : index + count = p.segmentLen) :
    RelCT isa (Related p pass lane slice index count old leftState rightState)
      Impl.Argon2.X86_64.FillSegment.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (index old : Nat) (leftState rightState : FillState),
    index + n = p.segmentLen ∧ 0 < n ∧ Related p pass lane slice index n old leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.FillSegment.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, counter, ls, rs, endIndex, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have blockRelated : FillBlock.Related p pass lane slice j counter ls rs s t :=
        ⟨hp.source, hp.leftMatrix, hp.rightMatrix,
          Proof.Argon2.segment_first_reference p pass lane slice j n ls rs
            hp.source.left.filling.bounds.active hp.indices⟩
      obtain ⟨trace, flags, next⟩ := body_rel p pass lane slice j counter ls rs _ _ _ _ _ _ blockRelated ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p pass lane slice j counter hp.source.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · simp only [eval, flags]
      · intro taken
        have active : j + 1 < p.segmentLen := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        obtain ⟨⟨nextCounter, ready⟩, matrixA, matrixB⟩ := next active
        have indices := hp.indices
        rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at indices
        exact ⟨n, by omega, j + 1, nextCounter, fillBlock p pass slice lane j ls,
          fillBlock p pass slice lane j rs, by omega, by omega, ready, matrixA, matrixB, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨index, old, leftState, rightState, endIndex, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.FillSegment

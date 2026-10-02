import VerifiedGarbage.Proof.Argon2.X86_64.FillIterations
import VerifiedGarbage.Proof.Argon2.X86_64.FillIterationsBodyCT
import VerifiedGarbage.Proof.Argon2.IterationsIndices

/-! The pass loop exposes only the complete filling reference log. -/

namespace VG.Proof.Argon2.X86_64.FillIterations

open VG VG.X86_64 VG.Spec.Argon2

structure Related (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  ready : NextRelated p pass leftState rightState s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.iterations p pass count leftState).indices =
    (Proof.Argon2.iterations p pass count rightState).indices

theorem loop_rel (p : Params) (pass count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endPass : pass + count = p.passes) :
    RelCT isa (Related p pass count leftState rightState) Impl.Argon2.X86_64.FillIterations.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (pass : Nat) (leftState rightState : FillState),
    pass + n = p.passes ∧ 0 < n ∧ Related p pass n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.FillIterations.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endPass, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have passIndices := Proof.Argon2.iterations_first_pass p j n ls rs
        hp.ready.left.filling.parameters.segment_bound.1 hp.indices
      obtain ⟨trace, flags, next⟩ := body_rel p j ls rs _ _ _ _ _ _ ⟨hp.ready, passIndices⟩ ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p j hp.ready.left ls hp.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · simp only [eval, flags]
      · intro taken
        have active : j + 1 < p.passes := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        have ready := next active
        have indices := hp.indices
        rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at indices
        exact ⟨n, by omega, j + 1, fillPass p ls j,
          fillPass p rs j, by omega, by omega, ready, ready.leftMatrix, ready.rightMatrix, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨pass, leftState, rightState, endPass, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.FillIterations

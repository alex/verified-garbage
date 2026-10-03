import VerifiedGarbage.Proof.Argon2.AArch64.FillSlices
import VerifiedGarbage.Proof.Argon2.AArch64.FillSlicesBodyCT
import VerifiedGarbage.Proof.Argon2.SlicesIndices

/-! The complete pass leaks only its reviewed reference log, including Argon2id's mode change. -/

namespace VG.Proof.Argon2.AArch64.FillSlices

open VG VG.AArch64 VG.Spec.Argon2

structure Related (p : Params) (pass slice count : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  states : NextRelated p pass slice leftState rightState s t
  indices : (Proof.Argon2.slices p pass slice count leftState).indices =
    (Proof.Argon2.slices p pass slice count rightState).indices

theorem loop_rel (p : Params) (pass slice count : Nat) (leftState rightState : FillState)
    (positive : 0 < count) (endSlice : slice + count = 4) :
    RelCT isa (Related p pass slice count leftState rightState) Impl.Argon2.AArch64.FillSlices.loop (fun _ _ => True) := by
  let I := fun n s t => ∃ (slice : Nat) (leftState rightState : FillState),
    slice + n = 4 ∧ 0 < n ∧ Related p pass slice n leftState rightState s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.FillSlices.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, ls, rs, endSlice, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      have sliceRelated : FillSlice.Related p pass j ls rs s t :=
        ⟨hp.states.left, hp.states.right, hp.states.bases, hp.states.stacks, hp.states.matrices, hp.states.work,
          hp.states.leftMatrix, hp.states.rightMatrix, Proof.Argon2.slices_first_lane_fold p pass j n ls rs
            hp.states.left.parameters.segment_bound.1 hp.indices⟩
      obtain ⟨trace, flags, next⟩ := body_rel p pass j ls rs _ _ _ _ _ _ sliceRelated ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p pass j hp.states.left ls hp.states.leftMatrix
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < 4 := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        have indices := hp.indices
        rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at indices
        exact ⟨n, by omega, j + 1, Proof.Argon2.lanes p pass j 0 p.lanes ls,
          Proof.Argon2.lanes p pass j 0 p.lanes rs, by omega, by omega, next active, indices⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨slice, leftState, rightState, endSlice, positive, h⟩) (fun _ _ h => h)

theorem pass_rel (p : Params) (pass : Nat) (leftState rightState : FillState) :
    RelCT isa (fun s t => NextRelated p pass 0 leftState rightState s t ∧
      (fillPass p leftState pass).indices = (fillPass p rightState pass).indices)
      Impl.Argon2.AArch64.FillSlices.loop (fun _ _ => True) := by
  refine (loop_rel p pass 0 4 leftState rightState (by decide) (by decide)).mono ?_ (fun _ _ h => h)
  intro s t h
  refine ⟨h.1, ?_⟩
  rw [Proof.Argon2.slices_pass p pass leftState, Proof.Argon2.slices_pass p pass rightState]
  exact h.2

end VG.Proof.Argon2.AArch64.FillSlices

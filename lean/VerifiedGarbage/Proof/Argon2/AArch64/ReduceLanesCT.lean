import VerifiedGarbage.Proof.Argon2.AArch64.ReduceLanesBodyCT

/-! The final reduction leaks only public matrix addresses and the public lane count. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2

theorem loop_rel (p : Params) (lane count : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.AArch64.ReduceLanes.loop
      (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftAcc rightAcc : Block), lane + n = p.lanes ∧ 0 < n ∧
    Related p lane leftMemory rightMemory leftAcc rightAcc s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.ReduceLanes.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, la, ra, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨trace, flags, next⟩ := body_rel p j leftMemory rightMemory la ra _ _ _ _ _ _ hp ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p j hp.left leftMemory la hp.leftRep
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < p.lanes := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        exact ⟨n, by omega, j + 1, _, _, by omega, by omega, next active⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftAcc, rightAcc, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.ReduceLanes

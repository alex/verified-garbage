import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLoop
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLaneCT

/-! # Both initialization loops count only pubNext matrix dimensions -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

theorem lanesLoop_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s₁ s₂ : State) (memory : Addr) (lanes q : Nat) (h₁ h₂ : List Byte)
    (space₁ : Space s₁ memory (1024 * (lanes * q)))
    (space₂ : Space s₂ memory (1024 * (lanes * q)))
    (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q) :
    RelCT isa (fun s t => LoopI s₁ memory lanes q 0 h₁ s ∧
      LoopI s₂ memory lanes q 0 h₂ t ∧ AgreeSaved s t)
      (.loop (lane name (HPrime.hash v)) .ne) AgreeSaved := by
  let I := fun n s t => ∃ j, n = lanes - j ∧ j < lanes ∧
    LoopI s₁ memory lanes q j h₁ s ∧ LoopI s₂ memory lanes q j h₂ t ∧ AgreeSaved s t
  have steps : ∀ n, RelCT isa (I n) (lane name (HPrime.hash v)) fun a b =>
      isa.eval .ne a = isa.eval .ne b ∧
      (isa.eval .ne a = some false → AgreeSaved a b) ∧
      (isa.eval .ne a = some true → ∃ m < n, I m a b) := by
    intro n s t trace₁ trace₂ a b hp e₁ e₂
    obtain ⟨j, rfl, hj, hs, ht, pub⟩ := hp
    have bound : 1024 * (j * q) + 2048 ≤ 1024 * (lanes * q) := by
      have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
      rw [Nat.add_mul, Nat.one_mul] at mul
      omega
    have related : RelatedLane memory (1024 * (lanes * q)) (1024 * (j * q)) s t :=
      ⟨⟨space₁.keeps hs.keeps, hs.destination⟩,
        ⟨space₂.keeps ht.keeps, ht.destination⟩, pub⟩
    obtain ⟨trace, pubNext⟩ := lane_rel v name memory _ _ bound _ _ _ _ _ _ related e₁ e₂
    obtain ⟨_, a', ea, ha⟩ := lane_step v name s₁ s memory lanes q j h₁
      space₁ hj lanesBound hq hs
    obtain ⟨_, b', eb, hb⟩ := lane_step v name s₂ t memory lanes q j h₂
      space₂ hj lanesBound hq ht
    obtain ⟨-, rfl⟩ := Exec.det e₁ ea
    obtain ⟨-, rfl⟩ := Exec.det e₂ eb
    refine ⟨trace, ?_, fun _ => pubNext, ?_⟩
    · simp only [eval, ha.2, hb.2]
    · intro taken
      have remaining : lanes - (j + 1) ≠ 0 := by
        intro zero
        simp only [eval, ha.2, zero, decide_true, Option.map_some,
          Bool.not_true, Option.some.injEq, Bool.false_eq_true] at taken
      exact ⟨lanes - (j + 1), by omega, j + 1, rfl, by omega, ha.1, hb.1, pubNext⟩
  exact (RelCT.loop I steps lanes).mono (fun _ _ hp =>
    ⟨0, by omega, lo, hp.1, hp.2.1, hp.2.2⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.MemoryInit

import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelMatrix
import VerifiedGarbage.Proof.Argon2.FillStep

/-! Relate the complete assembly step to the reviewed filling-state transition. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem update_spec (s : State) (p : Params) (pass lane slice index : Nat) (state : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (random : s.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory) :
    state.memory.set! (currentIndex p lane slice index) (nextBlock s p pass lane slice index state.memory) =
      (fillBlock p pass slice lane index state).memory := by
  rw [Proof.Argon2.FillStep.memory p pass lane slice index state active]
  unfold nextBlock referenceIndex
  rw [random]
  rfl

theorem code_spec_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks state.memory)
    (random : s.gpr .x0 = Proof.Argon2.FillStep.random p pass lane slice index state.memory) :
    WP isa Impl.Argon2.AArch64.FillKernel.code s fun t => Done s t p pass lane slice index ∧
      Proof.Argon2.Represents t.mem (matrix s) p.blocks (fillBlock p pass slice lane index state).memory := by
  refine (code_ok s p pass lane slice index ready).mono ?_
  intro t done
  have represented' := done.represents ready state.memory represented
  rw [update_spec s p pass lane slice index state ready.bounds.active random] at represented'
  exact ⟨done, represented'⟩

end VG.Proof.Argon2.AArch64.FillKernel

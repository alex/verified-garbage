import VerifiedGarbage.Proof.Argon2.X86.Derive.Reduce

/-!
# Argon2 on x86 (32-bit): the derivation is correct

`body_ok`: the body computes the parameters and H₀, initializes and fills
the memory, and writes the tag (`Spec.Argon2.derive`) to `out`; `correct`:
the whole function, in its frames, keeps the ABI's registers too.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Spec.Blake2 (bytesAt)

theorem body_nosp : NoSp Impl.Argon2.X86.Derive.body := NoSp.of_all (by lit_decide)

theorem body_stack : stackUse Impl.Argon2.X86.Derive.body = 84 := by lit_decide

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem body_ok : WP isa Impl.Argon2.X86.Derive.body (entry s₀) fun t => BodyDone s₀ t ∧
    bytesAt t.mem ((outP s₀).setWidth 64) (outL s₀) =
      Spec.Argon2.derive (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀) := by
  unfold Impl.Argon2.X86.Derive.body
  refine WP.seq ?_
  rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
  refine parameters_ok hp fun s₁ i₁ p₁ => WP.block_nil ?_
  refine WP.seq ((code_ok hp i₁ p₁).mono fun s₂ ⟨i₂, p₂, b₂⟩ => ?_)
  refine WP.seq ((memoryInit_ok hp i₂ p₂ b₂).mono fun s₃ ⟨i₃, p₃, m₃⟩ => ?_)
  refine WP.seq ((passes_ok hp (st := Spec.Argon2.initMemory (prm s₀)
    (Spec.Argon2.initialHash (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀))) ⟨i₃, p₃, m₃⟩).mono
    fun s₄ f₄ => ?_)
  rw [show itersN s₀ = (prm s₀).passes from rfl, Proof.Argon2.iterations_fill] at f₄
  refine WP.seq ((reduce_ok hp f₄.inv f₄.pr f₄.mem).mono fun s₅ ⟨i₅, _, b₅⟩ => ?_)
  refine (finalOutput_ok hp i₅).mono fun t ⟨it, ot⟩ => ⟨it.done hp, ?_⟩
  rw [ot, b₅, Spec.Argon2.derive, Proof.Argon2.finish_reduction]
  rfl

theorem correct : WP isa Impl.Argon2.X86.Derive.derive s₀ fun t => abiPreserved s₀ t ∧ deriveX86.post s₀ t :=
  frames_ok (by have := hp.esp_lo; omega) body_nosp (body_ok hp) fun t u q m => by
    show bytesAt u.mem _ _ = _
    rw [m]; exact q

end

end VG.Proof.Argon2.X86.Derive

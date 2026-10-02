import VerifiedGarbage.Proof.Argon2.X86_64.InitialBodyReviewedCT
import VerifiedGarbage.Proof.Argon2.X86_64.InitialBodyState

/-! Preserve precisely the reviewed leakage relation across parameter computation. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Initial

theorem ReviewedRelated.of_state {s₁ s₂ t₁ t₂ : State} {p : Params}
    (h : ReviewedRelated p s₁ s₂) (k₁ : SameFrame s₁ t₁) (k₂ : SameFrame s₂ t₂)
    (length₁ : t₁.gpr .r13 = BitVec.ofNat 64 p.laneLen)
    (length₂ : t₂.gpr .r13 = BitVec.ofNat 64 p.laneLen) : ReviewedRelated p t₁ t₂ := by
  refine ⟨h.left.of_state k₁ length₁, h.right.of_state k₂ length₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨k₁.hashSpace h.hashing.left.space,
      fun input hi => k₁.input (h.hashing.left.inputs input hi)⟩,
      ⟨k₂.hashSpace h.hashing.right.space,
      fun input hi => k₂.input (h.hashing.right.inputs input hi)⟩, ?_, ?_, ?_, ?_⟩
    · rw [k₁.bp, k₂.bp]; exact h.hashing.bp
    · rw [k₁.bx, k₂.bx]; exact h.hashing.bx
    · rw [k₁.sp, k₂.sp]; exact h.hashing.sp
    · intro d hd; rw [k₁.word d, k₂.word d]; exact h.hashing.words d hd
  · unfold FillKernel.matrix; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.matrices
  · unfold FinalOutput.output; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.outputs
  · unfold FinalOutput.work; rw [k₁.mem, k₂.mem, k₁.bp, k₂.bp]; exact h.works
  · unfold VG.Proof.Argon2.X86_64.InitialBody.references
    rw [k₁.inputBytes passwordOffset passwordLenOffset, k₂.inputBytes passwordOffset passwordLenOffset,
      k₁.inputBytes saltOffset saltLenOffset, k₂.inputBytes saltOffset saltLenOffset,
      k₁.inputBytes secretOffset secretLenOffset, k₂.inputBytes secretOffset secretLenOffset,
      k₁.inputBytes adOffset adLenOffset, k₂.inputBytes adOffset adLenOffset]
    exact h.references

end VG.Proof.Argon2.X86_64.InitialBody

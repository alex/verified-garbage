import VerifiedGarbage.Proof.Argon2.X86_64.InitialBodyCT
import VerifiedGarbage.Proof.Argon2.References

/-! Use exactly the flattened leakage allowance of the shared derive contract. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Initial

def references (p : Params) (s : State) : List Nat := Spec.Argon2.references p
  (Initial.inputBytes s passwordOffset passwordLenOffset)
  (Initial.inputBytes s saltOffset saltLenOffset)
  (Initial.inputBytes s secretOffset secretLenOffset)
  (Initial.inputBytes s adOffset adLenOffset)

structure ReviewedRelated (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  hashing : Initial.Related s t
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  references : references p s = references p t

theorem ReviewedRelated.related {p : Params} {s t : State} (h : ReviewedRelated p s t) : Related p s t := by
  refine ⟨h.left, h.right, h.hashing, h.matrices, h.outputs, h.works, ?_⟩
  have parameters := h.left.filling.environment.parameters
  have positive : 0 < p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p parameters.lanesPositive
    have minimum := parameters.segment_bound.1
    omega
  have indices := Proof.Argon2.references_injective p positive _ _ _ _ _ _ _ _ h.references
  unfold initial
  rw [Proof.Argon2.iterations_fill, Proof.Argon2.iterations_fill]
  exact indices

theorem reviewed_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (ReviewedRelated p) (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v)) (fun _ _ => True) :=
  (code_rel v name p).mono (fun _ _ h => h.related) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.InitialBody

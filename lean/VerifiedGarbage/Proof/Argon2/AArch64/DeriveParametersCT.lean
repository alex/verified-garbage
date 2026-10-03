import VerifiedGarbage.Proof.Argon2.AArch64.DeriveParameters
import VerifiedGarbage.Proof.Argon2.AArch64.ParametersCT
import VerifiedGarbage.Proof.Argon2.AArch64.InitialBodyReviewedState

/-! Parameter calculation followed by the complete body obeys the reviewed leakage. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64 VG.Spec.Argon2

structure ParametersRelated (p : Params) (s t : State) : Prop where
  left : Parameters.Ready p s
  right : Parameters.Ready p t
  body : InitialBody.ReviewedRelated p (dimensionState s p) (dimensionState t p)

theorem parameters_body_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (ParametersRelated p)
      (.seq Impl.Argon2.AArch64.Parameters.code
        (Impl.Argon2.AArch64.InitialBody.code name v.hash)) (fun _ _ => True) := by
  have preparation := (Parameters.code_rel.mono (P' := ParametersRelated p)
    (fun s t h => by
      have left := dimension_frame s p
      have right := dimension_frame t p
      exact ⟨left.bp.symm.trans (h.body.hashing.bp.trans right.bp),
        left.sp.symm.trans (h.body.hashing.sp.trans right.sp)⟩)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨Parameters.code_ok s p h.left, Parameters.code_ok t p h.right⟩)
  refine preparation.seq ((InitialBody.reviewed_rel v name p).mono ?_ (fun _ _ h => h))
  rintro a b ⟨_, s, t, h, ⟨length₁, keeps₁⟩, ⟨length₂, keeps₂⟩⟩
  exact h.body.of_state (parameters_frame p keeps₁) (parameters_frame p keeps₂) length₁ length₂

end VG.Proof.Argon2.AArch64.Derive

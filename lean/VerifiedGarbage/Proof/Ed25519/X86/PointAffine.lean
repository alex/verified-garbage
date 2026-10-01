import VerifiedGarbage.Impl.Ed25519.X86.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86.Power

/-! Untrusted: convert extended coordinates with the verified inversion chain. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩
theorem invEnv_x (e : Env) : invEnv e 0 = e 0 := rfl
theorem invEnv_y (e : Env) : invEnv e 1 = e 1 := rfl

theorem pointAffine_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointAffine s fun t => IKeep x s t ∧
      env t.mem x 0 = env s.mem x 0 * Spec.X25519.pow (env s.mem x 2) (Spec.X25519.P - 2) ∧
      env t.mem x 1 = env s.mem x 1 * Spec.X25519.pow (env s.mem x 2) (Spec.X25519.P - 2) := by
  refine WP.seq (WP.mono (invert_spec x s hc) fun u ⟨ku, eu⟩ => ?_)
  refine WP.mono (fieldCode_ok affineOps (ku.ctx hc)) fun t ⟨kt, et⟩ => ?_
  refine ⟨ku.trans (IKeep.of_field kt), ?_, ?_⟩
  · rw [et, (affine_eval _).1, eu, invEnv_x, invEnv_eval, VG.Proof.X25519.invert_eq]
  · rw [et, (affine_eval _).2, eu, invEnv_y, invEnv_eval, VG.Proof.X25519.invert_eq]

end VG.Proof.Ed25519.X86

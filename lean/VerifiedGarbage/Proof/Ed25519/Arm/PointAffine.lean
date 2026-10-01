import VerifiedGarbage.Impl.Ed25519.Arm.PointEncode
import VerifiedGarbage.Proof.Ed25519.Arm.Power

/-! Untrusted: affine conversion using the verified inversion chain. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem IKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : IKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩

theorem invEnv_xy (e : Env) : invEnv e 0 = e 0 ∧ invEnv e 1 = e 1 := by
  simp (config := {decide := true}) only [invEnv, power250Env, opMul, opSqn, Function.update_apply]
  exact ⟨rfl, rfl⟩

theorem pointAffine_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa pointAffine s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      env t.mem base 0 = env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) ∧
      env t.mem base 1 = env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) := by
  refine WP.seq (WP.mono (invert_spec base s hc hl) fun t ⟨hk, hlt, hv⟩ => ?_)
  refine WP.mono (fieldCode_ok affineOps (hk.ctx hc) hlt) fun u ⟨ku, hlu, vu⟩ => ?_
  refine ⟨hk.trans (IKeep.of_keep ku), hlu, ?_, ?_⟩
  · rw [vu, (affine_eval _).1, hv, (invEnv_xy _).1, invEnv_eval, Proof.X25519.invert_eq]
  · rw [vu, (affine_eval _).2, hv, (invEnv_xy _).2, invEnv_eval, Proof.X25519.invert_eq]

end VG.Proof.Ed25519.Arm

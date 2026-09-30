import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.X86.RecoverSign

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

private theorem eqOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := ⟨rfl, rfl, rfl, rfl⟩

theorem pointEqual_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointEqual s fun t => FieldKeep x s t ∧ t.gpr .eax = signWord
      (Spec.Ed25519.pointEqual (point (env s.mem x) 0 1 2 3) (point (env s.mem x) 4 5 6 7)) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hc) fun a ⟨ka, ea⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.ctx hc) 8 9) fun b ⟨kb, eb, zb⟩ => ?_
  have ab := (eqOps_eval (env s.mem x)).1
  have a9 := (eqOps_eval (env s.mem x)).2.1
  have a10 := (eqOps_eval (env s.mem x)).2.2.1
  have a11 := (eqOps_eval (env s.mem x)).2.2.2
  rw [ea, ab, a9] at zb
  apply WP.ite (decide (env s.mem x 0 * env s.mem x 6 = env s.mem x 4 * env s.mem x 2)) zb
  · intro heq
    refine WP.seq (WP.mono (fieldEqual_ok ((ka.trans kb).ctx hc) 10 11) fun c ⟨kc, _, zc⟩ => ?_)
    rw [eb 10 (by decide), eb 11 (by decide), ea, a10, a11] at zc
    apply WP.ite (decide (env s.mem x 1 * env s.mem x 6 = env s.mem x 5 * env s.mem x 2)) zc
    · intro heq'
      refine WP.mono (returnFlag_ok c x true) fun t ⟨kt, _, rt⟩ => ?_
      refine ⟨((ka.trans kb).trans kc).trans kt, ?_⟩
      have h := of_decide_eq_true heq
      have h' := of_decide_eq_true heq'
      simpa only [Spec.Ed25519.pointEqual, point, h, h', beq_self_eq_true, Bool.true_and] using rt
    · intro hne
      refine WP.mono (returnFlag_ok c x false) fun t ⟨kt, _, rt⟩ => ?_
      refine ⟨((ka.trans kb).trans kc).trans kt, ?_⟩
      have h := of_decide_eq_false hne
      simpa only [Spec.Ed25519.pointEqual, point, beq_eq_false_iff_ne.mpr h, Bool.and_false] using rt
  · intro hne
    refine WP.mono (returnFlag_ok b x false) fun t ⟨kt, _, rt⟩ => ?_
    refine ⟨(ka.trans kb).trans kt, ?_⟩
    have h := of_decide_eq_false hne
    simpa only [Spec.Ed25519.pointEqual, point, beq_eq_false_iff_ne.mpr h, Bool.false_and] using rt

end VG.Proof.Ed25519.X86

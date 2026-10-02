import VerifiedGarbage.Impl.Ed25519.Arm.PointEqual
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverSign

/-! Compare points exactly as the reviewed verification equation does. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem equalOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem pointEqual_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa Impl.Ed25519.Arm.pointEqual s fun t => Keep base s t ∧ AllLim t.mem base ∧
      t.gpr .r9 = BitVec.ofNat 32 (Spec.Ed25519.pointEqual (point (env s.mem base) 0 1 2 3)
        (point (env s.mem base) 4 5 6 7)).toNat := by
  refine WP.seq (WP.mono (fieldCode_ok pointEqualOps hc hl) fun a ⟨ka, la, va⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.ctx hc) la 8 9) fun b ⟨kb, lb, be, bz⟩ => ?_)
  have kab := ka.trans kb
  have bx : b.z = decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2) := by
    rw [bz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  apply WP.ite _ (congrArg some bx)
  · intro htx
    have hx := of_decide_eq_true htx
    refine WP.seq (WP.mono (fieldEqual_ok (kab.ctx hc) lb 10 11) fun c ⟨kc, lc, _, cz⟩ => ?_)
    have cy : c.z = decide (env s.mem base 1 * env s.mem base 6 = env s.mem base 5 * env s.mem base 2) := by
      rw [cz, be 10 (by decide), be 11 (by decide), va, (equalOps_eval _).2.2.1, (equalOps_eval _).2.2.2]
    apply WP.ite _ (congrArg some cy)
    · intro hty
      have hy := of_decide_eq_true hty
      refine WP.mono (returnFlag_ok c true) fun t ⟨tr, tm, tv⟩ => ?_
      refine ⟨(kab.trans kc).trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩, tm ▸ lc, ?_⟩
      simpa only [Spec.Ed25519.pointEqual, point, hx, hy, beq_self_eq_true, Bool.and_self] using tv
    · intro hfy
      have hy := of_decide_eq_false hfy
      refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tm, tr⟩ => ?_
      refine ⟨(kab.trans kc).trans kt, tm ▸ lc, ?_⟩
      simp only [Spec.Ed25519.pointEqual, point, hx, beq_self_eq_true, beq_eq_false_iff_ne.mpr hy,
        Bool.and_false, Bool.toNat_false]
      exact tr
  · intro hfx
    have hx := of_decide_eq_false hfx
    refine WP.mono (recoverInvalid_ok b base) fun t ⟨kt, tm, tr⟩ => ?_
    refine ⟨kab.trans kt, tm ▸ lb, ?_⟩
    simp only [Spec.Ed25519.pointEqual, point, beq_eq_false_iff_ne.mpr hx, Bool.false_and, Bool.toNat_false]
    exact tr

end VG.Proof.Ed25519.Arm

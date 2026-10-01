import VerifiedGarbage.Proof.Ed25519.Arm.VerifyHeaders

/-! Untrusted: combine R + [k]A and load [S]B for the final point comparison. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyCombine_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa verifyCombine s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b 8000 ∧
      point (env t.mem b) 4 5 6 7 = Spec.Ed25519.pointAdd (tablePoint s.mem b 7872)
        (point (env s.mem b) 0 1 2 3) := by
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc hl) fun a ⟨ak, al, ae⟩ => ?_)
  have aq := (congrArg (fun e => point e 4 5 6 7) ae).trans (copyPointToQ_eval _)
  have ad : env a.mem b 16 = Spec.Ed25519.d := by rw [ae, copyPointToQ_d, hd]
  refine WP.seq (WP.mono (pointTableRead_ok (ak.ctx hc) al 7872 (by decide) (by decide))
    fun c ⟨ck, cl, cp, ch⟩ => ?_)
  have kc := (AccKeep.of_keep ak).trans ck
  have cq : point (env c.mem b) 4 5 6 7 = point (env s.mem b) 0 1 2 3 :=
    (point_congr _ _ _ _ (ch 4 (by decide)) (ch 5 (by decide)) (ch 6 (by decide)) (ch 7 (by decide))).trans aq
  have cp' := cp.trans (workspace_tablePoint ak.frame (by decide) (by decide))
  refine WP.seq (WP.mono (pointAdd_ok (kc.ctx hc) cl ((ch 16 (by decide)).trans ad))
    fun d ⟨dk, dl, dp, _⟩ => ?_)
  have kd := kc.trans (AccKeep.of_keep dk)
  have dp' := dp.trans (congrArg₂ Spec.Ed25519.pointAdd cp' cq)
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps (kd.ctx hc) dl) fun e ⟨ek, el, ee⟩ => ?_)
  have ke := kd.trans (AccKeep.of_keep ek)
  have eqp := ((congrArg (fun f => point f 4 5 6 7) ee).trans (copyPointToQ_eval _)).trans dp'
  refine WP.mono (pointTableRead_ok (ke.ctx hc) el 8000 (by decide) (by decide))
    fun t ⟨tk, tl, tp, th⟩ => ?_
  exact ⟨ke.trans tk, tl, tp.trans (workspace_tablePoint ke.frame (by decide) (by decide)),
    (point_congr _ _ _ _ (th 4 (by decide)) (th 5 (by decide)) (th 6 (by decide)) (th 7 (by decide))).trans eqp⟩

end VG.Proof.Ed25519.Arm

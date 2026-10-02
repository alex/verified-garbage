import VerifiedGarbage.Proof.Ed25519.Arm.VerifyHeaders

/-! The left side of the equation is [S]B, retaining A and R. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyLhs_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyLhs s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      tablePoint t.mem b 8000 = Spec.Ed25519.pointMul
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint ∧
      tablePoint t.mem b 7744 = tablePoint s.mem b 7744 ∧
      tablePoint t.mem b 7872 = tablePoint s.mem b 7872 := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadHeader_ok hc.ctx 8132 (by decide)) fun a ⟨ar, am, ap⟩ => ?_
  refine WP.mono (addInput32_ok a) fun c ⟨cr, cm, cp⟩ => ?_
  have kc : PointKeep b s c := ⟨(ar.mono (by decide)).trans (cr.mono (by decide)), by
    rw [cm, am]; exact Frame.refl _ _⟩
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) (kc.ctx hc.ctx)
    (by rw [cm, am]; exact hl)) fun d ⟨dk, dl, de⟩ => ?_)
  have kd := kc.trans (PointKeep.of_keep dk)
  have dc := hc.keep (VerifyKeep.of_point kd)
  have di := dc.sigInput.suffix32
  have dp : d.gpr .r12 = sig + 32 := by rw [dk.rest.gpr _ (by decide), cp, ap, hc.sigHeader]
  have dpoint : point (env d.mem b) 0 1 2 3 = Spec.Ed25519.basePoint :=
    (congrArg (fun e => point e 0 1 2 3) de).trans (constPoint_eval _ _)
  refine WP.seq (WP.mono (pointFromScalar_ok dc.ctx dl dp 16 (by decide) (by decide)
    di.fit di.readable di.separate) fun e ⟨ek, el, _, ep⟩ => ?_)
  have ke := kd.trans ek
  have ep' : point (env e.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint := by
    rw [(hc.sigInput.suffix32).bytes (VerifyKeep.of_point kd), dpoint] at ep
    exact ep
  refine WP.mono (pointTableWrite_ok (ke.ctx hc.ctx) el 8000 (by decide) (by decide))
    fun t ⟨tk, tl, _, tp⟩ => ?_
  refine ⟨(VerifyKeep.of_point ke).trans (VerifyKeep.of_powers tk (by decide) (by decide)), tl,
    tp.trans ep', ?_, ?_⟩
  · exact (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans
      (ke.table (by decide) (by decide))
  · exact (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans
      (ke.table (by decide) (by decide))

end VG.Proof.Ed25519.Arm

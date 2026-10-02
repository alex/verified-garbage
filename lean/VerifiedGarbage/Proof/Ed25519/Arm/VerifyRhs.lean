import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCombine

/-! The right side reads all 512 challenge bits before the strict equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyRhs_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyRhs s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      t.gpr .r9 = BitVec.ofNat 32 (Spec.Ed25519.pointEqual (tablePoint s.mem b 8000)
        (Spec.Ed25519.pointAdd (tablePoint s.mem b 7872)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64))
            (tablePoint s.mem b 7744)))).toNat := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointTableRead_ok hc.ctx hl 7744 (by decide) (by decide)) fun a ⟨ak, al, ap, _⟩ => ?_
  refine WP.mono (loadHeader_ok (ak.ctx hc.ctx) 8136 (by decide)) fun c ⟨cr, cm, cp⟩ => ?_
  have kc := ak.trans (AccKeep.of_rest cr (by decide) cm)
  have cpk : PointKeep b s c := PointKeep.of_mul (MulKeep.of_powers (PowersKeep.of_acc kc))
  have cc := hc.keep (VerifyKeep.of_acc kc)
  have cp' : c.gpr .r12 = challenge := cp.trans (hc.keep (VerifyKeep.of_acc ak)).challengeHeader
  have capp : point (env c.mem b) 0 1 2 3 = tablePoint s.mem b 7744 :=
    (congrArg (fun m => point (env m b) 0 1 2 3) cm).trans ap
  refine WP.seq (WP.mono (pointFromScalar_ok cc.ctx (cm ▸ al) cp' 32 (by decide) (by decide)
    cc.challengeInput.fit cc.challengeInput.readable cc.challengeInput.separate) fun d ⟨dk, dl, dd, dp⟩ => ?_)
  have kd := cpk.trans dk
  have dp' : point (env d.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)) (tablePoint s.mem b 7744) := by
    rw [hc.challengeInput.bytes (VerifyKeep.of_acc kc), capp] at dp
    exact dp
  refine WP.seq (WP.mono (verifyCombine_ok (kd.ctx hc.ctx) dl dd) fun e ⟨ek, el, ep, eqp⟩ => ?_)
  have ep' := ep.trans (kd.table (by decide) (by decide))
  have eqp' := eqp.trans (congrArg₂ Spec.Ed25519.pointAdd (kd.table (by decide) (by decide)) dp')
  refine WP.mono (pointEqual_ok (ek.ctx (kd.ctx hc.ctx)) el) fun t ⟨tk, tl, tv⟩ => ?_
  refine ⟨((VerifyKeep.of_point kd).trans (VerifyKeep.of_acc ek)).trans (VerifyKeep.of_keep tk), tl, ?_⟩
  exact tv.trans (congrArg (fun v : Bool => BitVec.ofNat 32 v.toNat)
    (congrArg₂ Spec.Ed25519.pointEqual ep' eqp'))

end VG.Proof.Ed25519.Arm

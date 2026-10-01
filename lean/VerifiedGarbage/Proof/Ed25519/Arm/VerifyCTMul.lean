import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLhs

/-! Untrusted: verification multiplies A by every public challenge bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def verifyRhsMul : Prog isa :=
  .seq (.block (pointTableRead 7744 ++ loadHeader 8136)) (pointFromScalar 32)

theorem verifyLoadChallenge_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b))
      (.block (pointTableRead 7744 ++ loadHeader 8136))
      (fun s t => FromCTPre b challenge 32 s ∧ FromCTPre b challenge 32 t) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.ctx.r0.trans h.2.1.ctx.r0.symm
  · intro s ⟨hc, hl⟩
    rw [WP.block_append_iff]
    refine WP.mono (pointTableRead_ok hc.ctx hl 7744 (by decide) (by decide)) fun u ⟨uk, ul, _, _⟩ => ?_
    refine WP.mono (loadHeader_ok (uk.ctx hc.ctx) 8136 (by decide)) fun t ⟨tr, tm, tp⟩ => ?_
    have ku := VerifyKeep.of_acc uk
    have kt := ku.trans (VerifyKeep.of_rest tr (by decide) tm)
    have hi := (hc.keep kt).challengeInput
    exact ⟨kt.ctx hc.ctx, tm ▸ ul, tp.trans (hc.keep ku).challengeHeader, hi.fit, hi.readable, hi.separate⟩

theorem verifyRhsMul_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyContext b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyContext b pk sig challenge t ∧ AllLim t.mem b)) verifyRhsMul (fun _ _ => True) :=
  RelCT.seq (verifyLoadChallenge_ct b pk sig challenge) (pointFromScalar_ct b challenge 32 (.inr rfl))

theorem verifyRhsMul_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyRhsMul s fun t => PointKeep b s t ∧ AllLim t.mem b ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      point (env t.mem b) 0 1 2 3 = Spec.Ed25519.pointMul
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64)) (tablePoint s.mem b 7744) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointTableRead_ok hc.ctx hl 7744 (by decide) (by decide)) fun a ⟨ak, al, ap, _⟩ => ?_
  refine WP.mono (loadHeader_ok (ak.ctx hc.ctx) 8136 (by decide)) fun c ⟨cr, cm, cp⟩ => ?_
  have kc := ak.trans (AccKeep.of_rest cr (by decide) cm)
  have cpk := PointKeep.of_mul (MulKeep.of_powers (PowersKeep.of_acc kc))
  have cc := hc.keep (VerifyKeep.of_acc kc)
  have cp' : c.gpr .r12 = challenge := cp.trans (hc.keep (VerifyKeep.of_acc ak)).challengeHeader
  have capp : point (env c.mem b) 0 1 2 3 = tablePoint s.mem b 7744 :=
    (congrArg (fun m => point (env m b) 0 1 2 3) cm).trans ap
  refine WP.mono (pointFromScalar_ok cc.ctx (cm ▸ al) cp' 32 (by decide) (by decide)
    cc.challengeInput.fit cc.challengeInput.readable cc.challengeInput.separate) fun t ⟨tk, tl, td, tp⟩ => ?_
  refine ⟨cpk.trans tk, tl, td, ?_⟩
  rw [hc.challengeInput.bytes (VerifyKeep.of_acc kc), capp] at tp
  exact tp

end VG.Proof.Ed25519.Arm

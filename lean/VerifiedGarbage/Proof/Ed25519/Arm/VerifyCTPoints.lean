import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTRhs

/-! Untrusted: the strict equation has identical traces for identical public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def EquationCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7744 = a ∧ tablePoint s.mem b 7872 = r

theorem verifyLhs_public_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) :
    CT (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t)
      verifyLhs (fun s t => RhsCTPre m b pk sig challenge a r
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint) s ∧
        RhsCTPre m b pk sig challenge a r
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint) t) := by
  apply ctBoth
  · exact (verifyLhs_ct b pk sig challenge).mono (fun _ _ h =>
      ⟨⟨h.1.1.ctx, h.1.2.1⟩, ⟨h.2.1.ctx, h.2.2.1⟩⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, ha, hr⟩
    refine WP.mono (verifyLhs_ok hp.ctx hl) fun t ⟨tk, tl, tp, ta, tr⟩ => ?_
    exact ⟨hp.keep tk, tl, ta.trans ha, tr.trans hr,
      tp.trans (congrArg (fun bs => Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE bs) Spec.Ed25519.basePoint) hp.sBytes)⟩

theorem verifyEquationPoints_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) :
    CT (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t)
      verifyEquationPoints (fun _ _ => True) :=
  RelCT.seq (verifyLhs_public_ct m b pk sig challenge a r) (verifyRhs_ct m b pk sig challenge a r _)

end VG.Proof.Ed25519.Arm

import VerifiedGarbage.Proof.Ed25519.Arm.VerifyLhs
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyRhs

/-! Untrusted: compose both sides of the exact, uncofactored verification equation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def equationResult (m : Mem) (sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) : Bool :=
  Spec.Ed25519.pointEqual
    (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint)
    (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr challenge) 64)) a))

theorem verifyEquationPoints_ok {b pk sig challenge : BitVec 32} {s : State}
    (hc : VerifyContext b pk sig challenge s) (hl : AllLim s.mem b) :
    WP isa verifyEquationPoints s fun t => VerifyKeep b s t ∧ AllLim t.mem b ∧
      t.gpr .r9 = BitVec.ofNat 32 (equationResult s.mem sig challenge
        (tablePoint s.mem b 7744) (tablePoint s.mem b 7872)).toNat := by
  refine WP.seq (WP.mono (verifyLhs_ok hc hl) fun u ⟨uk, ul, up, ua, ur⟩ => ?_)
  refine WP.mono (verifyRhs_ok (hc.keep uk) ul) fun t ⟨tk, tl, tv⟩ => ?_
  refine ⟨uk.trans tk, tl, ?_⟩
  rw [up, ua, ur, hc.challengeInput.bytes uk] at tv
  exact tv

end VG.Proof.Ed25519.Arm

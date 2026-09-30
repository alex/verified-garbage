import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTArithmetic
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqualCT

/-! Untrusted: compare the shared public verification equation after fixed-trace multiplication. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem verifyRhsPrepare_ct (base pk sig challenge : Addr) :
    CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      verifyRhsPrepare (fun _ _ => True) := by
  rw [verifyRhsPrepare]
  exact CT.seq (verifyLoadChallenge_ct base pk sig challenge)
    (CT.seq (verifyReadA_ct base challenge)
      (CT.seq (scalarTrace_base 32 base challenge (by decide) (by decide)
        (pointFromScalar32_ct base challenge)) (verifyCombine_ct base)))

def RhsCTPre (base pk sig challenge : Addr) (a r lhs : Spec.Ed25519.Point) (k : Nat) (s : State) : Prop :=
  VerifyContext s base pk sig challenge ∧ tablePoint s.mem base 7424 = a ∧
    tablePoint s.mem base 7552 = r ∧ tablePoint s.mem base 7680 = lhs ∧
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64) = k

theorem verifyRhs_ct (base pk sig challenge : Addr) (a r lhs : Spec.Ed25519.Point) (k : Nat) :
    CT (fun s t => RhsCTPre base pk sig challenge a r lhs k s ∧
      RhsCTPre base pk sig challenge a r lhs k t) verifyRhs (fun _ _ => True) := by
  have ht := (verifyRhsPrepare_ct base pk sig challenge).mono
    (fun _ _ (h : RhsCTPre base pk sig challenge a r lhs k _ ∧
      RhsCTPre base pk sig challenge a r lhs k _) => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)
  have hw (s : State) (h : RhsCTPre base pk sig challenge a r lhs k s) :
      WP isa verifyRhsPrepare s (EqualCTPre base lhs (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a))) := by
    refine WP.mono (verifyRhsPrepare_ok h.1.scratch h.1.challengeHeader h.1.challengeRead h.1.challengeFar)
      fun t ⟨kt, tl, tr⟩ => ?_
    refine ⟨kt.scratch h.1.scratch, ?_, ?_⟩
    · exact tl.trans h.2.2.2.1
    · rw [tr, h.2.1, h.2.2.1, h.2.2.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [verifyRhs]
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (pointEqual_ct base lhs (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a)))

end VG.Proof.Ed25519.AArch64

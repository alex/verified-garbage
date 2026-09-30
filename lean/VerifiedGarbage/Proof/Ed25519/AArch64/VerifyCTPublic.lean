import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTRhs

/-! Untrusted: the verification inputs are public and survive every arithmetic stage. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

structure VerifyPublic (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (s : State) : Prop where
  context : VerifyContext s base pk sig challenge
  pkBytes : Spec.Ed25519.bytesAt s.mem pk 32 = pkbs
  rBytes : Spec.Ed25519.bytesAt s.mem sig 32 = rbs
  sBytes : Spec.Ed25519.bytesAt s.mem (off sig 32) 32 = sbs
  kBytes : Spec.Ed25519.bytesAt s.mem challenge 64 = kbs

theorem VerifyPublic.of_keep {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {s t : State}
    (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs s) (kt : VerifyKeep base s t) :
    VerifyPublic base pk sig challenge pkbs rbs sbs kbs t :=
  ⟨h.context.of_keep kt, (verifyKeep_bytes kt h.context.pkFar).trans h.pkBytes,
    (verifyKeep_bytes kt h.context.rFar).trans h.rBytes,
    (verifyKeep_bytes kt h.context.scalarFar).trans h.sBytes,
    (verifyKeep_bytes kt h.context.challengeFar).trans h.kBytes⟩

def PointsCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
    tablePoint s.mem base 7424 = a ∧ tablePoint s.mem base 7552 = r

theorem verifyEquationPoints_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) :
    CT (fun s t => PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r s ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r t) verifyEquationPoints (fun _ _ => True) := by
  have ht := (verifyLhs_ct base pk sig challenge).mono
    (fun _ _ (h : PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r _ ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r _) => ⟨h.1.1.context, h.2.1.context⟩) (fun _ _ h => h)
  have hw (s : State) (h : PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r s) :
      WP isa verifyLhs s (RhsCTPre base pk sig challenge a r
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE sbs) Spec.Ed25519.basePoint) (Spec.Ed25519.decodeLE kbs)) := by
    refine WP.mono (verifyLhs_ok h.1.context.scratch h.1.context.sigHeader h.1.context.scalarBytes h.1.context.scalarFar)
      fun t ⟨kt, tv, tp⟩ => ?_
    refine ⟨h.1.context.of_keep kt, (tp 7424 (by decide) (by decide)).trans h.2.1,
      (tp 7552 (by decide) (by decide)).trans h.2.2, ?_, ?_⟩
    · rw [tv, h.1.sBytes]
    · rw [(h.1.of_keep kt).kBytes]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [verifyEquationPoints]
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (verifyRhs_ct base pk sig challenge a r
      (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE sbs) Spec.Ed25519.basePoint) (Spec.Ed25519.decodeLE kbs))

end VG.Proof.Ed25519.AArch64

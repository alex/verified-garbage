import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTArithmetic
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTChallenge
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqualCT

/-! Untrusted: compare the shared public verification equation after fixed-trace multiplication. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem verifyLoadChallenge_ok {s : State} {base pk sig challenge : Addr} {k : Nat}
    (h : VerifyContext s base pk sig challenge ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64) = k) :
    WP isa (.block [ld .x1 7952]) s (ChallengeCTPre base challenge k) := by
  refine WP.mono (loadPointer_ok h.1.scratch .x1 7952 (by decide) (by decide)) fun t ⟨tp, kt⟩ => ?_
  exact ⟨⟨⟨h.1.scratch.of_keeps kt (by decide), tp.trans h.1.challengeHeader,
    fun i hi => by rw [kt.rd, kt.wr]; exact h.1.challengeRead i hi, h.1.challengeFar⟩,
    by rw [kt.mem]; exact h.2⟩, fun d hd => by rw [kt.rd, kt.wr]; exact h.1.challengeWords d hd⟩

theorem verifyReadAVar_ok {s : State} {base challenge : Addr} {k : Nat}
    (h : ChallengeCTPre base challenge k s) :
    WP isa (.block (pointTableRead 7424)) s (ChallengeCTPre base challenge k) :=
  WP.mono (pointTableRead_ok h.1.1.1 7424 (by decide) (by decide)) fun _ kt =>
    ⟨⟨h.1.1.of_counter kt.1, by rw [outside_bytes kt.1.mem (by decide) h.1.1.2.2.2]; exact h.1.2⟩,
      fun d hd => by rw [kt.1.rd, kt.1.wr]; exact h.2 d hd⟩

theorem verifyRhsPrepare_ct (base pk sig challenge : Addr) (k : Nat) :
    CT (fun s t => (VerifyContext s base pk sig challenge ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64) = k) ∧
      (VerifyContext t base pk sig challenge ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem challenge 64) = k))
      verifyRhsPrepare (fun _ _ => True) := by
  rw [verifyRhsPrepare]
  refine seq_runs ?_ (fun x h => verifyLoadChallenge_ok h) (fun y h => verifyLoadChallenge_ok h) ?_
  · exact (verifyLoadChallenge_ct base pk sig challenge).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
      (fun _ _ _ => trivial)
  refine seq_runs ?_ (fun x h => verifyReadAVar_ok h) (fun y h => verifyReadAVar_ok h) ?_
  · exact (verifyReadA_ct base challenge).mono (fun _ _ h => ⟨h.1.1.1, h.2.1.1⟩)
      (fun _ _ _ => trivial)
  have hm (s : State) (h : ChallengeCTPre base challenge k s) :
      WP isa challengeMul s fun t => t.gpr .x0 = base :=
    WP.mono (challengeMul_ok h.1.1.1 h.1.1.2.1 h.2 h.1.1.2.2.1 h.1.1.2.2.2)
      fun _ kt => (kt.1.scratch h.1.1.1).x0
  refine seq_runs (challengeMul_ct base challenge k) (fun x h => hm x h) (fun y h => hm y h) ?_
  exact verifyCombine_ct base

def RhsCTPre (base pk sig challenge : Addr) (a r lhs : Spec.Ed25519.Point) (k : Nat) (s : State) : Prop :=
  VerifyContext s base pk sig challenge ∧ tablePoint s.mem base 7424 = a ∧
    tablePoint s.mem base 7552 = r ∧ tablePoint s.mem base 7680 = lhs ∧
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64) = k

theorem verifyRhs_ct (base pk sig challenge : Addr) (a r lhs : Spec.Ed25519.Point) (k : Nat) :
    CT (fun s t => RhsCTPre base pk sig challenge a r lhs k s ∧
      RhsCTPre base pk sig challenge a r lhs k t) verifyRhs (fun _ _ => True) := by
  have ht := (verifyRhsPrepare_ct base pk sig challenge k).mono
    (fun _ _ (h : RhsCTPre base pk sig challenge a r lhs k _ ∧
      RhsCTPre base pk sig challenge a r lhs k _) => ⟨⟨h.1.1, h.1.2.2.2.2⟩, ⟨h.2.1, h.2.2.2.2.2⟩⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : RhsCTPre base pk sig challenge a r lhs k s) :
      WP isa verifyRhsPrepare s (EqualCTPre base lhs (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a))) := by
    refine WP.mono (verifyRhsPrepare_ok h.1.scratch h.1.challengeHeader h.1.challengeRead
      h.1.challengeWords h.1.challengeFar)
      fun t ⟨kt, tl, tr⟩ => ?_
    refine ⟨kt.scratch h.1.scratch, ?_, ?_⟩
    · exact tl.trans h.2.2.2.1
    · rw [tr, h.2.1, h.2.2.1, h.2.2.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [verifyRhs]
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (pointEqual_ct base lhs (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a)))

end VG.Proof.Ed25519.AArch64

import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTArithmetic
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqualCT

/-! Untrusted: compare the shared public verification equation after fixed-trace multiplication. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

theorem verifyLoadChallenge_ok {s : State} {base pk sig challenge : Addr} {k : Nat}
    (h : VerifyContext s base pk sig challenge ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64) = k) :
    WP isa (.block [.mov .rsi (.mem (Impl.X25519.X86_64.sc 7952))]) s
      (ScalarVarCTPre 32 base challenge k) := by
  refine WP.mono (loadPointer_ok h.1.scratch .rsi 7952 (by decide)) fun t ⟨tp, kt⟩ => ?_
  exact ⟨⟨h.1.scratch.of_keeps kt (by decide), tp.trans h.1.challengeHeader,
    fun i hi => by rw [kt.2.2.1, kt.2.2.2]; exact h.1.challengeRead i hi, h.1.challengeFar⟩,
    by rw [kt.2.1]; exact h.2⟩

theorem verifyReadAVar_ok {s : State} {base challenge : Addr} {k : Nat}
    (h : ScalarVarCTPre 32 base challenge k s) :
    WP isa (.block (pointTableRead 7424)) s (ScalarVarCTPre 32 base challenge k) :=
  WP.mono (pointTableRead_ok h.1.1 7424 (by decide) (by decide)) fun _ kt =>
    ⟨h.1.of_rbx kt.1, by rw [outside_bytes kt.1.mem (by decide) h.1.2.2.2]; exact h.2⟩

theorem verifyRhsPrepare_ct (base pk sig challenge : Addr) (k : Nat) :
    RelCT isa (fun s t => (VerifyContext s base pk sig challenge ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64) = k) ∧
      (VerifyContext t base pk sig challenge ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem challenge 64) = k))
      verifyRhsPrepare (fun _ _ => True) := by
  rw [verifyRhsPrepare]
  refine seq_runs ?_ (fun x h => verifyLoadChallenge_ok h) (fun y h => verifyLoadChallenge_ok h) ?_
  · exact (verifyLoadChallenge_ct base pk sig challenge).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
      (fun _ _ _ => trivial)
  refine seq_runs ?_ (fun x h => verifyReadAVar_ok h) (fun y h => verifyReadAVar_ok h) ?_
  · exact (verifyReadA_ct base challenge).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ _ => trivial)
  have hm (s : State) (h : ScalarVarCTPre 32 base challenge k s) :
      WP isa (pointFromScalarVar 32) s fun t => t.gpr .rdi = base :=
    WP.mono (pointFromScalarVar_ok h.1.1 h.1.2.1 32 (by decide) (by decide) h.1.2.2.1 h.1.2.2.2)
      fun _ kt => (kt.1.scratch h.1.1).rdi
  refine seq_runs (pointFromScalarVar32_ct base challenge k) (fun x h => hm x h) (fun y h => hm y h) ?_
  exact verifyCombine_ct base

def RhsCTPre (base pk sig challenge : Addr) (a r lhs : Spec.Ed25519.Point) (k : Nat) (s : State) : Prop :=
  VerifyContext s base pk sig challenge ∧ tablePoint s.mem base 7424 = a ∧
    tablePoint s.mem base 7552 = r ∧ tablePoint s.mem base 7680 = lhs ∧
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64) = k

theorem verifyRhs_ct (base pk sig challenge : Addr) (a r lhs : Spec.Ed25519.Point) (k : Nat) :
    RelCT isa (fun s t => RhsCTPre base pk sig challenge a r lhs k s ∧
      RhsCTPre base pk sig challenge a r lhs k t) verifyRhs (fun _ _ => True) := by
  have ht := (verifyRhsPrepare_ct base pk sig challenge k).mono
    (fun _ _ (h : RhsCTPre base pk sig challenge a r lhs k _ ∧
      RhsCTPre base pk sig challenge a r lhs k _) => ⟨⟨h.1.1, h.1.2.2.2.2⟩, ⟨h.2.1, h.2.2.2.2.2⟩⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : RhsCTPre base pk sig challenge a r lhs k s) :
      WP isa verifyRhsPrepare s (EqualCTPre base lhs (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a))) := by
    refine WP.mono (verifyRhsPrepare_ok h.1.scratch h.1.challengeHeader h.1.challengeRead h.1.challengeFar)
      fun t ⟨kt, tl, tr⟩ => ?_
    refine ⟨kt.scratch h.1.scratch, ?_, ?_⟩
    · exact tl.trans h.2.2.2.1
    · rw [tr, h.2.1, h.2.2.1, h.2.2.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [verifyRhs]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (pointEqual_ct base lhs (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a)))

end VG.Proof.Ed25519.X86_64

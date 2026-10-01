import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTDecode
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTSetup
import VerifiedGarbage.Proof.Ed25519.X86.VerifyMain

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verifyBody_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀) (.seq (.block verifyScalar) (.ite .e verifyDecodeA recoverInvalid))
      (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have hh := (verifyScalar_ct h).wp (fun _ _ hp =>
    ⟨verifyScalar_ok ps.scratch ps.scalar hp.1, verifyScalar_ok pt.scratch pt.scalar hp.2⟩)
  refine VG.RelCT.seq hh (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t hp
    change s.zf = t.zf
    rw [hp.2.1.2, hp.2.2.2, h.scalarFe]
  · exact (verifyDecodeA_ct h).mono (fun _ _ hp => ⟨hp.1.2.1.1, hp.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem verifyTail_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀)
      (.seq (.seq (.block verifyScalar) (.ite .e verifyDecodeA recoverInvalid)) (.block verifyFinish))
      (fun _ _ => True) := by
  have hh := (verifyBody_ct h).wp (fun _ _ hp =>
    ⟨verifyBody_ok (verify_pre h.left) hp.1, verifyBody_ok (verify_pre h.right) hp.2⟩)
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_) verifyFinish_ct
  intro s t hp
  exact hp.2.1.1.edi.trans ((h.args 3 (by decide)).trans hp.2.2.1.edi.symm)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have start := ctWithRuns verifyStart_ct (fun _ _ h =>
    ⟨abiSave_ok (verify_pre h.1).scratch, abiSave_ok (verify_pre h.2.1).scratch⟩)
  rw [verifyEquation]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact verifyTail_ct ⟨hp.1, hp.2.1, hp.2.2⟩ _ _ _ _ _ _ ⟨hu, hv⟩ es et

end VG.Proof.Ed25519.X86

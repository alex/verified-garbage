import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTAdjust
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverSign

/-! The negative-zero rejection depends only on the public coordinate and sign. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem signTestThen_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block signTest) (.ite .ne recoverInvalid recoverAdjustSign)) (fun _ _ => True) := by
  have ht : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block signTest) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block signTest) s fun t => SignCTPre base b x t ∧ t.z = !b := by
    refine WP.mono (signTest_ok h.1 b h.2.2.1) fun t ⟨tr, tm, tz⟩ => ?_
    exact ⟨⟨h.1.of_rest tr (by decide), tm ▸ h.2.1, tm ▸ h.2.2.1, tm ▸ h.2.2.2⟩, tz⟩
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    simp only [VG.Arm.eval, h.2.1.2, h.2.2.2]
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

theorem recoverSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t) recoverSign (fun _ _ => True) := by
  have ht : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (fieldZero 0) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (fieldZero 0) s fun t => SignCTPre base b x t ∧ t.z = decide (x = 0) := by
    refine WP.mono (fieldZero_ok h.1 h.2.1 0) fun t ⟨tk, tl, te, tz⟩ => ?_
    refine ⟨⟨tk.ctx h.1, tl, tk.sign.trans h.2.2.1, ?_⟩, ?_⟩
    · rw [te]; exact h.2.2.2
    · rw [tz, h.2.2.2]
  rw [recoverSign]
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.2.1.2.trans h.2.2.2.symm)
  · exact (signTestThen_ct base b x).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm

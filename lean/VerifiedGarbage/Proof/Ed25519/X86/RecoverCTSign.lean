import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTAdjust

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem testThenSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block [.alu .test .esi (.reg .esi)]) (.ite .ne recoverInvalid recoverAdjustSign))
      (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block [.alu .test .esi (.reg .esi)]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block [.alu .test .esi (.reg .esi)]) s fun t =>
        SignCTPre base b x t ∧ isa.eval .ne t = some b := by
    refine WP.mono (signTest_ok base b h.2.1) fun t ⟨kt, mt, zt⟩ => ?_
    exact ⟨⟨kt.ctx h.1, kt.keep.esi.trans h.2.1, by rw [mt]; exact h.2.2⟩, zt⟩
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

theorem recoverSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      recoverSign (fun _ _ => True) := by
  have ht := (zeroBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.edi, h.2.1.edi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldZero 0)) s fun t =>
        SignCTPre base b x t ∧ t.zf = some (decide (x = 0)) := by
    refine WP.mono (fieldZero_ok h.1 0) fun t ⟨kt, et, zt⟩ => ?_
    exact ⟨⟨kt.ctx h.1, kt.keep.esi.trans h.2.1, by rw [et]; exact h.2.2⟩,
      by rw [zt, h.2.2]⟩
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverSign]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (testThenSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

end VG.Proof.Ed25519.X86

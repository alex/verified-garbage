import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTSign

/-! Untrusted: the two square-root checks branch on public field values. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

def RootCTState (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  SignCTPre base b (rootX y) s ∧
    env s.mem base 11 = rootV y * rootX y * rootX y ∧
    env s.mem base 6 = rootU y ∧ env s.mem base 12 = 0 - rootU y

def rootCheckValue (y : Spec.X25519.Fe) (minus : Bool) : Bool :=
  decide (rootV y * rootX y * rootX y = if minus then 0 - rootU y else rootU y)

theorem rootCheck_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (minus : Bool) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual 11 (if minus then 12 else 6)))
      (fun s t => (RootCTState base b y s ∧ s.zf = some (rootCheckValue y minus)) ∧
        (RootCTState base b y t ∧ t.zf = some (rootCheckValue y minus))) := by
  have ht : RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual 11 (if minus then 12 else 6))) (fun _ _ => True) := by
    cases minus
    · apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
      exact fun _ _ h => edi_agree h.1.1.1.edi h.2.1.1.edi
    · apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
      exact fun _ _ h => edi_agree h.1.1.1.edi h.2.1.1.edi
  have hw (s : State) (h : RootCTState base b y s) :
      WP isa (.block (fieldEqual 11 (if minus then 12 else 6))) s fun t =>
        RootCTState base b y t ∧ t.zf = some (rootCheckValue y minus) := by
    refine WP.mono (fieldEqual_ok h.1.1 11 (if minus then 12 else 6)) fun t ⟨kt, te, tz⟩ => ?_
    refine ⟨⟨⟨kt.ctx h.1.1, kt.keep.esi.trans h.1.2.1,
      (te 0 (by decide)).trans h.1.2.2⟩, (te 11 (by decide)).trans h.2.1,
      (te 6 (by decide)).trans h.2.2.1, (te 12 (by decide)).trans h.2.2.2⟩, ?_⟩
    rw [tz, rootCheckValue, h.2.1]
    cases minus <;> simp only [Bool.false_eq_true, ite_false, ite_true, h.2.2.1, h.2.2.2]
  exact (VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem rootAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign)
      (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) s fun t =>
        SignCTPre base b (x * Spec.Ed25519.sqrtM1) t := by
    refine WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] h.1) fun t ⟨kt, te⟩ => ?_
    refine ⟨kt.ctx h.1, kt.keep.esi.trans h.2.1, ?_⟩
    rw [te]
    change env s.mem base 0 * Spec.Ed25519.sqrtM1 = _
    rw [h.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (recoverSign_ct base b (x * Spec.Ed25519.sqrtM1))

theorem recoverMinus_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual 11 12)) (.ite .e
        (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid))
      (fun _ _ => True) := by
  refine VG.RelCT.seq (rootCheck_ct base b y true) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (rootAdjustSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem recoverChecks_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual 11 6)) (.ite .e recoverSign
        (.seq (.block (fieldEqual 11 12)) (.ite .e
          (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid))))
      (fun _ _ => True) := by
  refine VG.RelCT.seq (rootCheck_ct base b y false) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (recoverSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact (recoverMinus_ct base b y).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)


end VG.Proof.Ed25519.X86

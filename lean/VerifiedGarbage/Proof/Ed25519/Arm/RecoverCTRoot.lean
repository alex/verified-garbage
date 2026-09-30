import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTSign
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverPoint

/-! Candidate validation branches only on the public encoded coordinate. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def RootCTState (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  SignCTPre base b (rootX y) s ∧ env s.mem base 11 = rootV y * rootX y * rootX y ∧
    env s.mem base 6 = rootU y ∧ env s.mem base 12 = 0 - rootU y

def rootCheckValue (y : Spec.X25519.Fe) (minus : Bool) : Bool :=
  decide (rootV y * rootX y * rootX y = if minus then 0 - rootU y else rootU y)

theorem rootCheck_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (minus : Bool) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (fieldEqual 11 (if minus then 12 else 6))
      (fun s t => (RootCTState base b y s ∧ s.z = rootCheckValue y minus) ∧
        (RootCTState base b y t ∧ t.z = rootCheckValue y minus)) := by
  apply ctBoth
  · cases minus
    · apply ctRegs [.r0] _ (by taint_decide)
      exact fun _ _ h => r0_agree h.1.1.1.r0 h.2.1.1.r0
    · apply ctRegs [.r0] _ (by taint_decide)
      exact fun _ _ h => r0_agree h.1.1.1.r0 h.2.1.1.r0
  · intro s h
    refine WP.mono (fieldEqual_ok h.1.1 h.1.2.1 11 (if minus then 12 else 6)) fun t ⟨kt, lt, te, tz⟩ => ?_
    refine ⟨⟨⟨kt.ctx h.1.1, lt, kt.sign.trans h.1.2.2.1,
      (te 0 (by decide)).trans h.1.2.2.2⟩, (te 11 (by decide)).trans h.2.1,
      (te 6 (by decide)).trans h.2.2.1, (te 12 (by decide)).trans h.2.2.2⟩, ?_⟩
    rw [tz, rootCheckValue, h.2.1]
    cases minus <;> simp only [Bool.false_eq_true, ite_false, ite_true, h.2.2.1, h.2.2.2]

theorem rootAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) recoverSign) (fun _ _ => True) := by
  have hp : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])
      (fun s t => SignCTPre base b (x * Spec.Ed25519.sqrtM1) s ∧ SignCTPre base b (x * Spec.Ed25519.sqrtM1) t) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
    · intro s h
      refine WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] h.1 h.2.1)
        fun t ⟨kt, lt, te⟩ => ?_
      refine ⟨kt.ctx h.1, lt, kt.sign.trans h.2.2.1, ?_⟩
      rw [te]
      change env s.mem base 0 * Spec.Ed25519.sqrtM1 = _
      rw [h.2.2.2]
  exact RelCT.seq hp (recoverSign_ct base b (x * Spec.Ed25519.sqrtM1))

theorem recoverMinus_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (fieldEqual 11 12) (.ite .eq
        (.seq (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) recoverSign) recoverInvalid)) (fun _ _ => True) := by
  refine RelCT.seq (rootCheck_ct base b y true) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (rootAdjustSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem recoverChecks_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (fieldEqual 11 6) (.ite .eq recoverSign
        (.seq (fieldEqual 11 12) (.ite .eq
          (.seq (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) recoverSign) recoverInvalid)))) (fun _ _ => True) := by
  refine RelCT.seq (rootCheck_ct base b y false) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (recoverSign_ct base b (rootX y)).mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact (recoverMinus_ct base b y).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)

def RecoverCTPre (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧
    s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat ∧ env s.mem base 1 = y

theorem recoverPoint_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RecoverCTPre base b y s ∧ RecoverCTPre base b y t) recoverPoint (fun _ _ => True) := by
  have hp : CT (fun s t => RecoverCTPre base b y s ∧ RecoverCTPre base b y t)
      recoverCandidate (fun s t => RootCTState base b y s ∧ RootCTState base b y t) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
    · intro s h
      refine WP.mono (recoverCandidate_ok h.1 h.2.1) fun t ⟨kt, lt, tx, _, _, tu, _, tv, tn⟩ => ?_
      refine ⟨⟨kt.ctx h.1, lt, kt.sign.trans h.2.2.1, ?_⟩, ?_, ?_, ?_⟩
      · rw [tx, h.2.2.2]
      · rw [tv, h.2.2.2]
      · rw [tu, h.2.2.2]
      · rw [tn, h.2.2.2]
  exact RelCT.seq hp (recoverChecks_ct base b y)

end VG.Proof.Ed25519.Arm

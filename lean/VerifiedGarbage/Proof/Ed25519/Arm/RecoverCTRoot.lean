import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverAdjust
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverSign
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverPoint

/-! Merged from `Proof.Ed25519.Arm.RecoverCTSign`. -/
section
/-! Merged from `Proof.Ed25519.Arm.RecoverCTAdjust`. -/
section
/-! The sign-adjustment branch depends only on the public coordinate and sign. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def SignCTPre (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧
    s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat ∧ env s.mem base 0 = x

theorem parityBlockCT_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block (freeze 0 ++ recoverParity)) s fun t =>
      Ctx base t ∧ t.z = (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hc hl 0) fun a ⟨ak, _, _, af, av⟩ => ?_
  refine WP.mono (recoverParity_ok (ak.ctx hc) b af (ak.sign.trans hb)) fun t ⟨tr, _, tz⟩ => ?_
  exact ⟨(ak.ctx hc).of_rest tr (by decide), by rw [tz, av]⟩

theorem adjustTail_ct :
    CT (fun x y => x.gpr .r0 = y.gpr .r0 ∧ x.z = y.z)
      (.seq (.ite .eq (.block []) (fieldCode [.const 5 0, .sub 0 5 0])) recoverSuccess) (fun _ _ => True) := by
  refine RelCT.seq (R := fun (x y : State) => ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r)
    (RelCT.ite (fun _ _ h => congrArg some h.2) ?_ ?_) ?_
  · apply ctRegsKeeping [.r0] [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1
  · apply ctRegsKeeping [.r0] [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1
  · apply ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => h

theorem recoverAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t) recoverAdjustSign (fun _ _ => True) := by
  have ht : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block (freeze 0 ++ recoverParity)) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (freeze 0 ++ recoverParity)) s fun t =>
        Ctx base t ∧ t.z = ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlockCT_ok h.1 h.2.1 b h.2.2.1) fun t ⟨hc, hz⟩ => ?_
    exact ⟨hc, by rw [hz, h.2.2.2]⟩
  have hp := (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h)
    (fun _ _ h => And.intro (h.2.1.1.r0.trans h.2.2.1.r0.symm) (h.2.1.2.trans h.2.2.2.symm))
  exact RelCT.seq hp adjustTail_ct

end VG.Proof.Ed25519.Arm
end

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
end

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

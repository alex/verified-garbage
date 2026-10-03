import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86.VerifyContract

/-! Merged from `Proof.Ed25519.X86.RecoverCTRoot`. -/
section
/-! Merged from `Proof.Ed25519.X86.RecoverCTSign`. -/
section
/-! Merged from `Proof.Ed25519.X86.RecoverCTAdjust`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def SignCTPre (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Ctx base s ∧ s.gpr .esi = signWord b ∧ env s.mem base 0 = x

theorem parityBlock_ok {s : State} {base : BitVec 32} (hs : Ctx base s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa (.block (Impl.X25519.X86.freeze 64 ++ recoverParity)) s fun t =>
      FieldKeep base s t ∧ t.zf = some (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hs 0) fun a ⟨ka, _, va⟩ => ?_
  refine WP.mono (recoverParity_ok (ka.ctx hs) b (ka.keep.esi.trans hb)) fun t ⟨kt, _, tz⟩ => ?_
  refine ⟨ka.trans kt, ?_⟩
  change fe a.mem base 64 = _ at va
  rw [tz, va]

theorem adjustTail_ct (base : BitVec 32) :
    RelCT isa (fun s t => Ctx base s ∧ Ctx base t ∧ s.zf = t.zf)
      (.seq (.ite .e (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0])))
        (.block recoverSuccess)) (fun _ _ => True) := by
  refine VG.RelCT.seq (M := isa) (R := fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
    (VG.RelCT.ite (fun _ _ h => h.2.2) ?_ ?_) (successBlock_ct base)
  · intro s t ts tt s' t' h es et
    rw [Exec.block_iff] at es et
    change some (s, []) = some (s', ts) at es
    change some (t, []) = some (t', tt) at et
    cases es; cases et
    exact ⟨rfl, h.1.1.edi, h.1.2.1.edi⟩
  · have ct := (negateBlock_ct base).mono
      (P' := fun (s t : State) => (Ctx base s ∧ Ctx base t ∧ s.zf = t.zf) ∧ isa.eval .e s = some false)
      (fun _ _ h => ⟨h.1.1.edi, h.1.2.1.edi⟩) (fun _ _ h => h)
    have hwp := ct.wp (fun _ _ h =>
      ⟨WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.1) (fun _ k => (k.1.ctx h.1.1).edi),
       WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.2.1) (fun _ k => (k.1.ctx h.1.2.1).edi)⟩)
    exact hwp.mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem recoverAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      recoverAdjustSign (fun _ _ => True) := by
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (Impl.X25519.X86.freeze 64 ++ recoverParity)) s fun t =>
        Ctx base t ∧ t.zf = some ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlock_ok h.1 b h.2.1) fun t ⟨kt, tz⟩ => ?_
    exact ⟨kt.ctx h.1, by rw [tz, h.2.2]⟩
  have ht := (parityBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.edi, h.2.1.edi⟩)
    (fun _ _ h => h)
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverAdjustSign]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)) (adjustTail_ct base)

end VG.Proof.Ed25519.X86
end

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
end

/-! The two square-root checks branch on public field values. -/

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
end

/-! Merged from `Proof.Ed25519.X86.PointDecodeCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.RecoverCTPoint`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def RecoverCTPre (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  Ctx base s ∧ wd s.mem base 32 = signWord b ∧ env s.mem base 1 = y

private def CandidateCTState (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  Ctx base s ∧ wd s.mem base 32 = signWord b ∧ env s.mem base 0 = rootX y ∧
    env s.mem base 11 = rootV y * rootX y * rootX y ∧
    env s.mem base 6 = rootU y ∧ env s.mem base 12 = 0 - rootU y

theorem recoverPoint_ct (base : BitVec 32) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RecoverCTPre base b y s ∧ RecoverCTPre base b y t)
      recoverPoint (fun _ _ => True) := by
  have ht := (recoverCandidate_ct base).mono
    (fun _ _ (h : RecoverCTPre base b y _ ∧ RecoverCTPre base b y _) => ⟨h.1.1.edi, h.2.1.edi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : RecoverCTPre base b y s) :
      WP isa recoverCandidate s (CandidateCTState base b y) := by
    refine WP.mono (recoverCandidate_ok h.1) fun t ⟨kt, tx, _, _, tu, _, tv, tn⟩ => ?_
    refine ⟨kt.ctx h.1, (kt.word h.1 32 (by decide)).trans h.2.1, ?_, ?_, ?_, ?_⟩
    · rw [tx, h.2.2]
    · rw [tv, h.2.2]
    · rw [tu, h.2.2]
    · rw [tn, h.2.2]
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have loadct : RelCT isa (fun s t => CandidateCTState base b y s ∧ CandidateCTState base b y t)
      (.block [.mov .esi (.mem (Impl.X25519.X86.sc 32))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have loadwp (s : State) (h : CandidateCTState base b y s) :
      WP isa (.block [.mov .esi (.mem (Impl.X25519.X86.sc 32))]) s (RootCTState base b y) := by
    refine Wp.wp_ldm h.1.edi (h.1.inRW (by decide) (by decide)) fun t kt => WP.block_nil ?_
    have kb : t.gpr .esi = signWord b := kt.gpr.trans h.2.1
    have ke := (IKeep.of_counter kt).ctx h.1
    refine ⟨⟨ke, kb, ?_⟩, ?_, ?_, ?_⟩
    · rw [kt.mem]; exact h.2.2.1
    · rw [kt.mem]; exact h.2.2.2.1
    · rw [kt.mem]; exact h.2.2.2.2.1
    · rw [kt.mem]; exact h.2.2.2.2.2
  have lp := loadct.wp (fun s t h => ⟨loadwp s h.1, loadwp t h.2⟩)
  rw [recoverPoint]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.seq (lp.mono (fun _ _ h => h) (fun _ _ h => h.2)) (recoverChecks_ct base b y))

end VG.Proof.Ed25519.X86
end

/-! Decoding branches only on the shared public compressed point. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def DecodeCTPre (base : BitVec 32) (n : Nat) (s : State) : Prop := Ctx base s ∧ fe s.mem base 96 = n

theorem decodeHeadCT_ok {base : BitVec 32} {s : State} (hc : Ctx base s) :
    WP isa (.block (decodeY ++ canonicalY)) s fun t =>
      RecoverCTPre base (fe s.mem base 96 / 2 ^ 255 == 1)
        (VG.Proof.X25519.toFe (fe s.mem base 96 % 2 ^ 255)) t ∧
      t.zf = some (decide (fe s.mem base 96 % 2 ^ 255 < Spec.X25519.P)) := by
  rw [WP.block_append_iff]
  refine WP.mono (decodeY_ok hc) fun a ⟨ka, ya, ba⟩ => ?_
  have ca := ka.ctx hc
  refine WP.mono (canonicalY_ok ca (by rw [ya]; exact Nat.mod_lt _ (by decide))) fun t ⟨kt, et, bt, zt⟩ => ?_
  refine ⟨⟨kt.ctx ca, ?_, ?_⟩, ?_⟩
  · rw [bt, ba]
    have hn : fe s.mem base 96 / 2 ^ 255 ≤ 1 := by
      have hlt := fe_lt s.mem base 96
      omega_using [hlt]
    rcases (by omega_using [hn] : fe s.mem base 96 / 2 ^ 255 = 0 ∨ fe s.mem base 96 / 2 ^ 255 = 1) with h | h
    all_goals rw [h]; rfl
  · rw [et]
    change VG.Proof.X25519.toFe (fe a.mem base 96) = _
    rw [ya]
  · rw [zt, ya]

theorem pointDecode_ct (base : BitVec 32) (n : Nat) :
    RelCT isa (fun s t => DecodeCTPre base n s ∧ DecodeCTPre base n t) pointDecode (fun _ _ => True) := by
  let b := n / 2 ^ 255 == 1
  let y := VG.Proof.X25519.toFe (n % 2 ^ 255)
  have ht : RelCT isa (fun s t => DecodeCTPre base n s ∧ DecodeCTPre base n t)
      (.block (decodeY ++ canonicalY)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : DecodeCTPre base n s) :
      WP isa (.block (decodeY ++ canonicalY)) s fun t =>
        RecoverCTPre base b y t ∧ t.zf = some (decide (n % 2 ^ 255 < Spec.X25519.P)) := by
    have hh := decodeHeadCT_ok h.1
    rw [h.2] at hh
    exact hh
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [pointDecode]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (recoverPoint_ct base b y).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .eax = signWord p.isSome := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def VerifySaved (s₀ t₀ s t : State) : Prop := Saved s₀ (arg s₀ 3) s ∧ Saved t₀ (arg t₀ 3) t

structure VerifyCTFacts (s t : State) : Prop where
  left : verifyLocal.pre s
  right : verifyLocal.pre t
  pub : verifyLocal.pub s t

theorem VerifyCTFacts.args {s t : State} (h : VerifyCTFacts s t) (i : Nat) (hi : i < 4) : arg s i = arg t i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  exacts [h.pub.2.1, h.pub.2.2.1, h.pub.2.2.2.1, h.pub.2.2.2.2.1]

theorem loadSlicePointer_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i skip : Nat)
    (hi : i ≤ 2) (hk : skip = 0 ∨ skip = 32) :
    RelCT isa (VerifySaved s₀ t₀) (.block (loadSlicePointer i skip))
      (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi) := by
  have hc : RelCT isa (VerifySaved s₀ t₀) (.block (loadSlicePointer i skip)) (fun _ _ => True) := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    all_goals rcases hk with rfl | rfl
    all_goals
      apply VG.RelCT.taint (A := taint) (regsTaint [.esp]) _ (by taint_decide)
      intro s t hp
      exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
        (hp.1.esp.trans (h.pub.1.trans hp.2.esp.symm)))
  have hp := ctWithRuns hc (fun _ _ hs => ⟨loadSlicePointer_ok (verify_pre h.left).scratch hs.1 (by omega),
    loadSlicePointer_ok (verify_pre h.right).scratch hs.2 (by omega)⟩)
  apply hp.mono (fun _ _ h => h)
  intro s t ⟨_, a, b, _, hs, ht⟩
  exact ⟨hs.1.edi.trans ((h.args 3 (by decide)).trans ht.1.edi.symm),
    hs.2.1.trans ((congrArg (· + BitVec.ofNat 32 skip) (h.args i (by omega))).trans ht.2.1.symm)⟩

theorem copyWords96_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
    (.block (copyWords 96 8)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
  intro s t h
  apply regsTaint_agree
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h.1, h.2]

theorem inputSlice96_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i : Nat) (hi : i ≤ 2) :
    RelCT isa (VerifySaved s₀ t₀) (.block (inputSliceWords i 0 96 8)) (fun _ _ => True) := by
  exact ctBlockAppend (loadSlicePointer_ct h i 0 hi (Or.inl rfl)) copyWords96_ct

theorem verifyScalar_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀) (.block verifyScalar) (fun _ _ => True) := by
  have hc : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (copyWords 64 8 ++ scalarSubtract ++ ([.alu .test .ebx (.reg .ebx)] : List Instr))) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2]
  simp only [verifyScalar, inputSliceWords, List.append_assoc]
  exact ctBlockAppend (loadSlicePointer_ct h 1 32 (by decide) (Or.inr rfl)) hc

theorem verifyFinish_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi)
    (.block verifyFinish) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  intro s t h
  exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)

end VG.Proof.Ed25519.X86

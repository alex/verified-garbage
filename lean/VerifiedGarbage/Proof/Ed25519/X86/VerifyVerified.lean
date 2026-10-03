import VerifiedGarbage.Proof.Ed25519.X86.VerifyDecode
import VerifiedGarbage.Proof.Ed25519.X86.VerifyScalar
import VerifiedGarbage.Proof.Ed25519.X86.VerifyFinish
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyDecodeInput
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTEquation
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTInputs
import VerifiedGarbage.Proof.Ed25519.X86.VerifyContract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Ed25519.X86.VerifyLit

/-! Merged from `Proof.Ed25519.X86.VerifyMain`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verificationScalar_num {s : State} (hp : VerifyPre s) :
    verificationScalar s = fe s.mem (arg s 1 + 32) 0 := by
  rw [verificationScalar, ← addr_zero (arg s 1 + BitVec.ofNat 32 32)]
  exact decode_words s.mem 8 (by have := hp.scalar.fit; omega_using [this])

private theorem verification_order (pk sig ch : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : ch.length = 64) :
    Spec.Ed25519.verifyEquation pk sig ch =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        (match Spec.Ed25519.decodePoint pk with
        | none => false
        | some a => match Spec.Ed25519.decodePoint (sig.take 32) with
          | none => false
          | some r => Spec.Ed25519.pointEqual
            (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (sig.drop 32)) Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE ch) a)))) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  cases Spec.Ed25519.decodePoint pk <;> cases Spec.Ed25519.decodePoint (sig.take 32) <;>
    simp only [Bool.and_false]

theorem verifyEquation_result {s : State} (hp : VerifyPre s) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64) =
      (decide (verificationScalar s < Spec.Ed25519.L) && decodeResult s) := by
  have address : (arg s 1 + BitVec.ofNat 32 32).setWidth 64 = (arg s 1).setWidth 64 + BitVec.ofNat 64 32 :=
    addr_eq (by have hf := hp.signature_fit; omega_using [hf])
  rw [verification_order _ _ _
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]),
    signatureBytes_take, signatureBytes_drop, ← address]
  have zero (i : Nat) : arg s i + BitVec.ofNat 32 0 = arg s i := BitVec.add_zero _
  simp only [decodeResult, decodeRResult, inputPoint, equationResult, verificationScalar,
    verificationChallenge, zero]
  cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32) <;>
    cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) <;> rfl

theorem verifyBody_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa (.seq (.block verifyScalar) (.ite .e verifyDecodeA recoverInvalid)) s fun t =>
      Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord
        (decide (verificationScalar s₀ < Spec.Ed25519.L) && decodeResult s₀) := by
  refine WP.seq (WP.mono (verifyScalar_ok hp.scratch hp.scalar hs) fun a ⟨ha, za⟩ => ?_)
  rw [← verificationScalar_num hp] at za
  apply WP.ite (decide (verificationScalar s₀ < Spec.Ed25519.L)) za
  · intro hh
    refine WP.mono (verifyDecodeA_ok hp ha) fun t ⟨ht, vt⟩ => ⟨ht, ?_⟩
    rw [hh, Bool.true_and]
    exact vt
  · intro hh
    refine WP.mono (recoverInvalid_ok a (arg s₀ 3)) fun t ⟨kt, rt⟩ => ?_
    exact ⟨ha.ikeep hp.scratch.fit (IKeep.of_field kt), by rw [hh, Bool.false_and]; exact rt⟩

theorem verify_correct {s : State} (h : verifyLocal.pre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  have hp := verify_pre h
  refine WP.seq (WP.mono (abiSave_ok hp.scratch) fun a ha => ?_)
  refine WP.seq (WP.mono (verifyBody_ok hp ha) fun b ⟨hb, vb⟩ => ?_)
  refine WP.mono (verifyFinish_ok hp.scratch hb) fun t ⟨abi_t, vt, _⟩ => ⟨abi_t, ?_⟩
  change t.gpr .eax = _
  rw [vt, vb, verifyEquation_result hp]

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.VerifyCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyCTDecode`. -/
section
/-! Merged from `Proof.Ed25519.X86.DecodedThenCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyCTDecodeInput`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem inputSliceValue_ok {s₀ s : State} {i : Nat} (hp : ScratchPre s₀ 3 4)
    (hi : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 0) 32)
    (hs : Saved s₀ (arg s₀ 3) s) (hia : i < 4) :
    WP isa (.block (inputSliceWords i 0 96 8)) s fun t => Saved s₀ (arg s₀ 3) t ∧
      fe t.mem (arg s₀ 3) 96 = Spec.Ed25519.decodeLE
        (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32) := by
  refine WP.mono (inputSliceWords_ok hp hi hs hia (by decide) (by decide) (by decide)) fun t ⟨ht, wt, _⟩ => ?_
  refine ⟨ht, ?_⟩
  rw [← addr_zero (arg s₀ i + BitVec.ofNat 32 0), decode_words s₀.mem 8 (by have := hi.fit; omega_using [this])]
  apply num_congr
  intro k hk
  simp only [Nat.zero_add]
  exact congrArg BitVec.toNat (wt k hk)

theorem decodeInput_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i : Nat) (hi : i ≤ 2)
    (is : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 0) 32)
    (it : SlicePre t₀ 3 (arg t₀ i + BitVec.ofNat 32 0) 32)
    (hb : Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t₀.mem ((arg t₀ i + BitVec.ofNat 32 0).setWidth 64) 32) :
    RelCT isa (VerifySaved s₀ t₀) (.seq (.block (inputSliceWords i 0 96 8)) pointDecode) (fun _ _ => True) := by
  have hh := (inputSlice96_ct h i hi).wp (fun _ _ hp =>
    ⟨inputSliceValue_ok (verify_pre h.left).scratch is hp.1 (by omega),
      inputSliceValue_ok (verify_pre h.right).scratch it hp.2 (by omega)⟩)
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (pointDecode_ct (arg s₀ 3) (Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32)))
  intro s t hp
  have hs := hp.2.1
  have ht := hp.2.2
  have left : DecodeCTPre (arg s₀ 3) _ s :=
    ⟨hs.1.ctx (verify_pre h.left).scratch.fit (verify_pre h.left).scratch.wr, hs.2⟩
  have right : DecodeCTPre (arg t₀ 3) (Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32)) t :=
    ⟨ht.1.ctx (verify_pre h.right).scratch.fit (verify_pre h.right).scratch.wr,
      ht.2.trans (congrArg Spec.Ed25519.decodeLE hb.symm)⟩
  exact ⟨left, Eq.mp (congrArg (fun base => DecodeCTPre base
    (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32)) t)
    (h.args 3 (by decide)).symm) right⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure TestUnchanged (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Saved.test {s₀ s t : State} {base : BitVec 32} (h : Saved s₀ base s) (k : TestUnchanged s t) : Saved s₀ base t :=
  ⟨(congrFun k.gpr _).trans h.edi, (congrFun k.gpr _).trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr,
    by rw [k.mem]; exact h.frame, by rw [k.mem]; exact h.saved⟩

theorem DecodeResult.test {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s t : State}
    (h : DecodeResult base p s) (k : TestUnchanged s t) : DecodeResult base p t := by
  cases p with
  | none => exact (congrFun k.gpr _).trans h
  | some p => exact ⟨(congrFun k.gpr _).trans h.1, by rw [k.mem]; exact h.2⟩

theorem decodedThen_ct (base : BitVec 32) (p : Option Spec.Ed25519.Point) (P₁ P₂ : State → Prop) (next : Prog isa)
    (hP₁ : ∀ s t, TestUnchanged s t → P₁ s → P₁ t)
    (hP₂ : ∀ s t, TestUnchanged s t → P₂ s → P₂ t)
    (hn : ∀ a, p = some a → RelCT isa
      (fun s t => (P₁ s ∧ point (env s.mem base) 0 1 2 3 = a) ∧
        (P₂ t ∧ point (env t.mem base) 0 1 2 3 = a)) next (fun _ _ => True)) :
    RelCT isa (fun s t => (P₁ s ∧ DecodeResult base p s) ∧ (P₂ t ∧ DecodeResult base p t))
      (decodedThen next) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => (P₁ s ∧ DecodeResult base p s) ∧ (P₂ t ∧ DecodeResult base p t))
      (.block [.alu .test .eax (.reg .eax)]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)
  have hw (P : State → Prop) (hP : ∀ s t, TestUnchanged s t → P s → P t) (s : State)
      (h : P s ∧ DecodeResult base p s) :
      WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t => P t ∧ DecodeResult base p t ∧ t.zf = some (!p.isSome) := by
    refine Wp.wp_test fun t kt zt => WP.block_nil ?_
    have k : TestUnchanged s t := ⟨kt.gpr, kt.mem, kt.rd, kt.wr⟩
    refine ⟨hP s t k h.1, h.2.test k, ?_⟩
    rw [zt, BitVec.and_self, decodeResult_flag h.2]
    cases p <;> rfl
  have hp := ht.wp (fun s t h => ⟨hw P₁ hP₁ s h.1, hw P₂ hP₂ t h.2⟩)
  rw [decodedThen]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t h
    change s.zf.map Bool.not = t.zf.map Bool.not
    rw [h.2.1.2.2, h.2.2.2.2]
  · cases p with
    | none =>
      apply VG.RelCT.of_false
      intro s t h
      have he := h.2
      change s.zf.map Bool.not = some true at he
      rw [h.1.2.1.2.2] at he
      contradiction
    | some a =>
      exact (hn a rfl).mono
        (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.1.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem VerifyCTFacts.inputA {s t : State} (h : VerifyCTFacts s t) : inputPoint s 0 = inputPoint t 0 :=
  congrArg Spec.Ed25519.decodePoint h.pkBytes

theorem VerifyCTFacts.inputR {s t : State} (h : VerifyCTFacts s t) : inputPoint s 1 = inputPoint t 1 :=
  congrArg Spec.Ed25519.decodePoint h.rBytes

def DecodeRCTPre (s₀ : State) (a : Spec.Ed25519.Point) (s : State) : Prop :=
  Saved s₀ (arg s₀ 3) s ∧ tablePoint s.mem (arg s₀ 3) 7680 = a

theorem pointTableWrite_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (o : Nat) (ho : o = 7680 ∨ o = 7808) :
    RelCT isa (VerifySaved s₀ t₀) (.block (pointTableWrite o)) (fun _ _ => True) := by
  rcases ho with rfl | rfl
  all_goals
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  all_goals exact fun _ _ hp => regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
    (hp.1.edi.trans ((h.args 3 (by decide)).trans hp.2.edi.symm)))

theorem verifyStoreR_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a r : Spec.Ed25519.Point) :
    RelCT isa (fun s t => (DecodeRCTPre s₀ a s ∧ point (env s.mem (arg s₀ 3)) 0 1 2 3 = r) ∧
      (DecodeRCTPre t₀ a t ∧ point (env t.mem (arg s₀ 3)) 0 1 2 3 = r))
      (.seq (.block (pointTableWrite 7808)) verifyEquationPoints) (fun _ _ => True) := by
  have hc := (pointTableWrite_ct h 7808 (Or.inr rfl)).mono
    (P' := fun (s t : State) => (DecodeRCTPre s₀ a s ∧ point (env s.mem (arg s₀ 3)) 0 1 2 3 = r) ∧
      (DecodeRCTPre t₀ a t ∧ point (env t.mem (arg s₀ 3)) 0 1 2 3 = r))
    (fun _ _ hp => ⟨hp.1.1.1, hp.2.1.1⟩) (fun _ _ h => h)
  have hw (u s : State) (hu : VerifyPre u) (hs : DecodeRCTPre u a s)
      (hr : point (env s.mem (arg u 3)) 0 1 2 3 = r) :
      WP isa (.block (pointTableWrite 7808)) s (EquationCTPre u a r) := by
    refine WP.mono (pointTableWrite_ok (hs.1.ctx hu.scratch.fit hu.scratch.wr) 7808 (by decide) (by decide))
      fun t ⟨kt, ft, pt⟩ => ?_
    refine ⟨hs.1.of_offset hu.scratch.fit kt ft (by decide) (by decide) (by decide), ?_, pt.trans hr⟩
    exact (tablePoint_frame hu.scratch.fit ft (by decide) (by decide) (Or.inl (by decide))).trans hs.2
  have hh := hc.wp (fun s t hp => ⟨hw s₀ s (verify_pre h.left) hp.1.1 hp.1.2,
    hw t₀ t (verify_pre h.right) hp.2.1 ((h.args 3 (by decide)) ▸ hp.2.2)⟩)
  exact VG.RelCT.seq (hh.mono (fun _ _ h => h) (fun _ _ h => h.2)) (verifyEquationPoints_ct h a r)

theorem verifyDecodeR_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a : Spec.Ed25519.Point) :
    RelCT isa (fun s t => DecodeRCTPre s₀ a s ∧ DecodeRCTPre t₀ a t) verifyDecodeR (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have hc := (decodeInput_ct h 1 (by decide) ps.r pt.r h.rBytes).mono
    (P' := fun (s t : State) => DecodeRCTPre s₀ a s ∧ DecodeRCTPre t₀ a t)
    (fun _ _ hp => ⟨hp.1.1, hp.2.1⟩) (fun _ _ h => h)
  have hw (u s : State) (hu : VerifyPre u) (hs : DecodeRCTPre u a s) :
      WP isa (.seq (.block (inputSliceWords 1 0 96 8)) pointDecode) s fun t =>
        DecodeRCTPre u a t ∧ DecodeResult (arg u 3) (inputPoint u 1) t := by
    refine WP.mono (decodeInput_ok hu.scratch hu.r hs.1 (by decide)) fun t ht => ?_
    have ha := (tablePoint_frame hu.scratch.fit ht.2.1 (by decide) (by decide) (Or.inr (by decide))).trans hs.2
    have hpre : DecodeRCTPre u a t := ⟨ht.1, ha⟩
    with_reducible exact ⟨hpre, ht.2.2⟩
  have hh := hc.wp (fun s t hp => ⟨hw s₀ s ps hp.1, hw t₀ t pt hp.2⟩)
  rw [verifyDecodeR]
  apply VG.RelCT.assoc
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (decodedThen_ct (arg s₀ 3) (inputPoint s₀ 1) (DecodeRCTPre s₀ a) (DecodeRCTPre t₀ a)
      (.seq (.block (pointTableWrite 7808)) verifyEquationPoints) ?_ ?_ ?_)
  · intro s t hp
    with_reducible refine ⟨hp.2.1, hp.2.2.1, ?_⟩
    with_reducible exact Eq.mp (congrArg₂ (fun base p => DecodeResult base p t)
      (h.args 3 (by decide)).symm h.inputR.symm) hp.2.2.2
  · intro s t k hp
    exact ⟨hp.1.test k, by rw [k.mem]; exact hp.2⟩
  · intro s t k hp
    exact ⟨hp.1.test k, by rw [k.mem]; exact hp.2⟩
  · intro r _
    exact verifyStoreR_ct h a r

theorem verifyStoreA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a : Spec.Ed25519.Point) :
    RelCT isa (fun s t => (Saved s₀ (arg s₀ 3) s ∧ point (env s.mem (arg s₀ 3)) 0 1 2 3 = a) ∧
      (Saved t₀ (arg t₀ 3) t ∧ point (env t.mem (arg s₀ 3)) 0 1 2 3 = a))
      (.seq (.block (pointTableWrite 7680)) verifyDecodeR) (fun _ _ => True) := by
  have hc := (pointTableWrite_ct h 7680 (Or.inl rfl)).mono
    (P' := fun (s t : State) => (Saved s₀ (arg s₀ 3) s ∧ point (env s.mem (arg s₀ 3)) 0 1 2 3 = a) ∧
      (Saved t₀ (arg t₀ 3) t ∧ point (env t.mem (arg s₀ 3)) 0 1 2 3 = a))
    (fun _ _ hp => ⟨hp.1.1, hp.2.1⟩) (fun _ _ h => h)
  have hw (u s : State) (hu : VerifyPre u) (hs : Saved u (arg u 3) s)
      (ha : point (env s.mem (arg u 3)) 0 1 2 3 = a) :
      WP isa (.block (pointTableWrite 7680)) s (DecodeRCTPre u a) := by
    refine WP.mono (pointTableWrite_ok (hs.ctx hu.scratch.fit hu.scratch.wr) 7680 (by decide) (by decide))
      fun t ⟨kt, ft, pt⟩ => ?_
    exact ⟨hs.of_offset hu.scratch.fit kt ft (by decide) (by decide) (by decide), pt.trans ha⟩
  have hh := hc.wp (fun s t hp => ⟨hw s₀ s (verify_pre h.left) hp.1.1 hp.1.2,
    hw t₀ t (verify_pre h.right) hp.2.1 ((h.args 3 (by decide)) ▸ hp.2.2)⟩)
  exact VG.RelCT.seq (hh.mono (fun _ _ h => h) (fun _ _ h => h.2)) (verifyDecodeR_ct h a)

theorem verifyDecodeA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀) verifyDecodeA (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have hh := ctWithRuns (decodeInput_ct h 0 (by decide) ps.pk pt.pk h.pkBytes)
    (fun _ _ hp => ⟨decodeInput_ok ps.scratch ps.pk hp.1 (by decide),
      decodeInput_ok pt.scratch pt.pk hp.2 (by decide)⟩)
  rw [verifyDecodeA]
  apply VG.RelCT.assoc
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (decodedThen_ct (arg s₀ 3) (inputPoint s₀ 0) (Saved s₀ (arg s₀ 3)) (Saved t₀ (arg t₀ 3))
      (.seq (.block (pointTableWrite 7680)) verifyDecodeR) ?_ ?_ ?_)
  · intro s t ⟨_, _, _, _, hs, ht⟩
    with_reducible refine ⟨⟨hs.1, hs.2.2⟩, ht.1, ?_⟩
    with_reducible exact Eq.mp (congrArg₂ (fun base p => DecodeResult base p t)
      (h.args 3 (by decide)).symm h.inputA.symm) ht.2.2
  · intro s t k hp; exact hp.test k
  · intro s t k hp; exact hp.test k
  · intro a _; exact verifyStoreA_ct h a

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.VerifyCTSetup`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def verifyEntryTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 20 }

theorem verifyEntryTaint_wf {s : State} (h : verifyLocal.pre s) : VG.X86.Taint.Wf verifyEntryTaint s := by
  have hp := (verify_pre h).scratch
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (by cases h),
    fun _ h => (by cases h), fun _ => ⟨?_, ?_⟩, fun _ h => (by cases h)⟩
  · exact hp.sp_fit
  · intro r hr
    rw [h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro a _ ha
      change _ + 1 ≤ 0 at ha
      omega_using [ha]
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.sp_fit; omega_using [this]) hp.ret_sc hp.args_sc

theorem verifyEntryTaint_agree {s t : State} (h : VerifyCTFacts s t) : VG.X86.Taint.Agree verifyEntryTaint s t := by
  refine ⟨⟨?_, fun h => (by cases h)⟩, fun h => absurd rfl h,
    verifyEntryTaint_wf h.left, verifyEntryTaint_wf h.right,
    fun _ h => (by cases h), fun _ h => (by cases h), fun _ => h.pub.1, ?_⟩
  · intro r hr
    simp only [verifyEntryTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r
    exact h.pub.1
  · intro k h4 hk
    change k < 20 at hk
    rw [show VG.X86.Taint.depth verifyEntryTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (verify_pre h.left).scratch.sp_fit h4 hk,
      VG.X86.Taint.argByte_eq (verify_pre h.right).scratch.sp_fit h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (h.args ((k - 4) / 4) (by omega_using [hk, h4]))

theorem verifyStart_ct : RelCT isa
    (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
    (.block (abiSave 3)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) verifyEntryTaint _ (by taint_decide)
  exact fun _ _ h => verifyEntryTaint_agree ⟨h.1, h.2.1, h.2.2⟩

end VG.Proof.Ed25519.X86
end

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
end

/-! Merged from `Proof.Ed25519.X86.VerifyNarrow`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyWide`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def verifyWide : Contract isa :=
  { verifyLocal with
  pre := fun s =>
    let pk := sub (arg s 0) 0 32
    let sig := sub (arg s 1) 0 64
    let challenge := sub (arg s 2) 0 64
    let scratch := scR 8192 (arg s 3)
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [pk, sig, challenge] ∧ s.wr = [scratch, args] ∧
      pk.Disjoint scratch ∧ sig.Disjoint scratch ∧ challenge.Disjoint scratch ∧
      args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

def verifyRd (s : State) : List Region :=
  [sub (arg s 0) 0 32, sub (arg s 1) 0 64, sub (arg s 2) 0 64, ⟨argAddr s 0, 16⟩]
def verifyWr (s : State) : List Region := [sub (arg s 3) 0 0, scR 8192 (arg s 3)]

theorem verifyWide_pre (s : State) (h : verifyWide.pre s) :
    verifyLocal.pre (s.withRegions (verifyRd s) (verifyWr s)) := by
  simp only [verifyLocal, verifyRd, verifyWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

def verifySatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else
    if a = 0x800d then 0x30 else if a = 0x8011 then 0x40 else 0

def verifySatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := verifySatMem
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8004, 16⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verifyWide_implies : verifyWide.Implies (Spec.Ed25519.verifyEquationContract X86.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyWide, verifyLocal, sub, addr_zero,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    change t.gpr .eax = signWord _ at h
    rw [h, BitVec.setWidth_append_eq_right]
    generalize Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨sp, bytes, pk, sig, challenge, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    exact ⟨sp, pk, sig, challenge, base, first, middle, last⟩
  sat := by
    have a0 : arg verifySatState 0 = 0x1000 := by decide
    have a1 : arg verifySatState 1 = 0x2000 := by decide
    have a2 : arg verifySatState 2 = 0x3000 := by decide
    have a3 : arg verifySatState 3 = 0x4000 := by decide
    have e : argAddr verifySatState 0 = 0x8004 := by decide
    have esp : verifySatState.gpr .esp = 0x8000 := rfl
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyWide, verifyLocal, sub, addr_zero,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, e, esp] using verifySatState

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86

theorem verifyNarrow_read (s : State) (h : verifyWide.pre s) (a : Addr) (n : Nat)
    (hr : InRegions (verifyRd s ++ verifyWr s) a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := hr
  rw [h.1, h.2.1]
  simp only [verifyRd, verifyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl)
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩
  · refine ⟨scR 8192 (arg s 3), by simp, ?_⟩
    simp only [addr_zero, Region.Contains] at hc ⊢
    omega_using [hc]
  · exact ⟨_, by simp, hc⟩

theorem verifyNarrow_write (s : State) (h : verifyWide.pre s) (a : Addr) (n : Nat)
    (hr : InRegions (verifyWr s) a n) : InRegions s.wr a n := by
  obtain ⟨r, hr, hc⟩ := hr
  rw [h.2.1]
  simp only [verifyWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨scR 8192 (arg s 3), by simp, ?_⟩
    simp only [addr_zero, Region.Contains] at hc ⊢
    omega_using [hc]
  · exact ⟨_, by simp, hc⟩

end VG.Proof.Ed25519.X86
end

/-! Transfer the verifier from its framed local contract to the reviewed ABI. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verify_verified_of_correct
    (correct : ∀ s, verifyLocal.pre s → WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t)
    (ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation) :
    Verified X86.target verifyEquation (Spec.Ed25519.verifyEquationContract X86.abi) := by
  have hsat := verifyWide_implies.sat_left
  have satLocal : ∃ s, verifyLocal.pre s := hsat.elim fun s h => ⟨_, verifyWide_pre s h⟩
  have verifiedLocal : Verified X86.target verifyEquation verifyLocal :=
    Verified.of_correct correct ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal verifyRd verifyWr verifyWide_pre
    verifyNarrow_read verifyNarrow_write ?_ ?_ hsat) verifyWide_implies
  · intro s t _ h
    simpa only [verifyWide, verifyLocal, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [verifyWide, verifyLocal, arg_withRegions, State.withRegions_gpr, State.withRegions_mem] using h

theorem verify_verified : Verified X86.target verifyEquation
    (Spec.Ed25519.verifyEquationContract X86.abi) :=
  verify_verified_of_correct (fun _ h => verify_correct h) verify_ct

end VG.Proof.Ed25519.X86

import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTInputs
import VerifiedGarbage.Proof.Ed25519.X86.PointCTMul
import VerifiedGarbage.Proof.Ed25519.X86.PointFromInput
import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Merged from `Proof.Ed25519.X86.VerifyCTMultiply`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verifyWr_agree {s t : State} (h : VerifyCTFacts s t) : s.wr = t.wr := by
  rw [h.left.2.1, h.right.2.1, h.args 3 (by decide)]

theorem verifyPointCtx_saved {s₀ s : State} (h : verifyLocal.pre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    PointCTCtx (arg s₀ 3) s := by
  have hp := (verify_pre h).scratch
  refine ⟨hs.ctx hp.fit hp.wr, ?_, ?_, ?_, ?_⟩
  · rw [hs.wr, h.2.1]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · rw [hs.wr, h.2.1]
    refine List.pairwise_cons.mpr ⟨?_, by simp⟩
    intro r hr a ha _
    change _ + 1 ≤ 0 at ha
    omega_using [ha]
  · intro r hr
    rw [hs.wr, h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [addr_zero, BitVec.toNat_setWidth]
    · omega_using [hp.fit]
    · omega_using [hp.fit]
  · change s.wr.getD 1 ⟨0, 0⟩ = _
    rw [hs.wr, h.2.1]; rfl

def sliceScalar (s : State) (i skip bytes : Nat) : Nat :=
  Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem ((arg s i + BitVec.ofNat 32 skip).setWidth 64) bytes)

theorem pointFromInputPrepareCT_ok {s₀ s : State} {i skip bytes count : Nat}
    (h : verifyLocal.pre s₀) (hi : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 skip) bytes)
    (hs : Saved s₀ (arg s₀ 3) s) (hia : i < 4) (hn : bytes ≤ 64)
    (hc32 : count ≤ 32) (hsize : 8 * bytes = 16 * count) :
    WP isa (.block (inputSliceBits i skip bytes ++ fieldCode [.const 16 Spec.Ed25519.d])) s fun t =>
      Saved s₀ (arg s₀ 3) t ∧ MulCTInput (arg s₀ 3) (sliceScalar s₀ i skip bytes) count t := by
  have hp := (verify_pre h).scratch
  refine WP.block_append (WP.mono (inputSliceBits_ok hp hi hs hia hn) fun a ⟨ha, ba, _⟩ => ?_)
  have ca := ha.ctx hp.fit hp.wr
  refine WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] ca) fun b ⟨kb, eb⟩ => ?_
  have hb := ha.ikeep hp.fit (IKeep.of_field kb)
  refine ⟨hb, verifyPointCtx_saved h hb, ?_, ?_, ?_⟩
  · have hh := decodeLE_lt (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 skip).setWidth 64) bytes)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at hh
    change sliceScalar s₀ i skip bytes < 256 ^ bytes at hh
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul, hsize] at hh
    exact hh
  · intro k hk
    rw [IKeep.bit (IKeep.of_field kb) ca k (by omega_using [hk, hc32]), ba k (by omega_using [hk, hsize]), scalarBit_nat]
    rfl
  · rw [eb]; rfl

theorem pointFromInput_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i skip bytes count : Nat)
    (hi : i ≤ 2) (hk : skip = 0 ∨ skip = 32) (hb : bytes = 32 ∨ bytes = 64)
    (hn : count = 16 ∨ count = 32) (hsize : 8 * bytes = 16 * count)
    (is : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 skip) bytes)
    (it : SlicePre t₀ 3 (arg t₀ i + BitVec.ofNat 32 skip) bytes) :
    RelCT isa (VerifySaved s₀ t₀) (pointFromInput i skip bytes count) (fun _ _ => True) := by
  have tailct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (expandScalarBits bytes ++ fieldCode [.const 16 Spec.Ed25519.d])) (fun _ _ => True) := by
    rcases hb with rfl | rfl
    all_goals
      apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
      intro s t h
      apply regsTaint_agree
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h.1, h.2]
  have prepct : RelCT isa (VerifySaved s₀ t₀)
      (.block (inputSliceBits i skip bytes ++ fieldCode [.const 16 Spec.Ed25519.d])) (fun _ _ => True) := by
    simp only [inputSliceBits, List.append_assoc]
    exact ctBlockAppend (loadSlicePointer_ct h i skip hi hk) tailct
  have prep := ctWithRuns prepct (fun _ _ hs =>
    ⟨pointFromInputPrepareCT_ok h.left is hs.1 (by omega) (by omega) (by omega) hsize,
     pointFromInputPrepareCT_ok h.right it hs.2 (by omega) (by omega) (by omega) hsize⟩)
  rw [pointFromInput]
  refine VG.RelCT.seq (prep.mono (fun _ _ h => h) ?_)
    (pointMultiply_ct (arg s₀ 3) (sliceScalar s₀ i skip bytes) (sliceScalar t₀ i skip bytes) count hn)
  intro s t ⟨_, a, b, _, hs, ht⟩
  exact ⟨hs.2, (h.args 3 (by decide)).symm ▸ ht.2,
    hs.1.wr.trans ((verifyWr_agree h).trans ht.1.wr.symm)⟩

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointEqualCT`. -/
section
/-! Point comparison branches only on the two public projective points. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

private theorem ctEqualOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := ⟨rfl, rfl, rfl, rfl⟩

def EqualCTPre (base : BitVec 32) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  Ctx base s ∧ point (env s.mem base) 0 1 2 3 = p ∧ point (env s.mem base) 4 5 6 7 = q

theorem equalFirst_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
      FieldKeep base s t ∧
      t.zf = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.ctx hs) 8 9) fun t ⟨kt, te, tz⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_, ?_⟩
  · rw [tz, va, (ctEqualOps_eval _).1, (ctEqualOps_eval _).2.1]
  · rw [te 10 (by decide), va, (ctEqualOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (ctEqualOps_eval _).2.2.2]

theorem returnFlag_ct (b : Bool) :
    RelCT isa (fun _ _ => True) (.block [.mov .eax (.imm (if b then 1 else 0))]) (fun _ _ => True) := by
  cases b
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)

theorem equalSecond_ct (base : BitVec 32) (u v : Spec.X25519.Fe) :
    RelCT isa (fun s t => (Ctx base s ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Ctx base t ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.seq (.block (fieldEqual 10 11)) (.ite .e (.block [.mov .eax (.imm 1)]) recoverInvalid))
      (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => (Ctx base s ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Ctx base t ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.block (fieldEqual 10 11)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : Ctx base s ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) :
      WP isa (.block (fieldEqual 10 11)) s fun t => t.zf = some (decide (u = v)) := by
    refine WP.mono (fieldEqual_ok h.1 10 11) fun _ k => ?_
    rw [k.2.2, h.2.1, h.2.2]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.trans h.2.2.symm
  · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem pointEqual_ct (base : BitVec 32) (p q : Spec.Ed25519.Point) :
    RelCT isa (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      Impl.Ed25519.X86.pointEqual (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : EqualCTPre base p q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        Ctx base t ∧ t.zf = some (decide (p.X * q.Z = q.X * p.Z)) ∧
          env t.mem base 10 = p.Y * q.Z ∧ env t.mem base 11 = q.Y * p.Z := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨kt.ctx h.1, ?_, ?_, ?_⟩
    · rw [tz, ← h.2.1, ← h.2.2]; rfl
    · rw [tu, ← h.2.1, ← h.2.2]; rfl
    · rw [tv, ← h.2.1, ← h.2.2]; rfl
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [Impl.Ed25519.X86.pointEqual]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · exact (equalSecond_ct base (p.Y * q.Z) (q.Y * p.Z)).mono
      (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem VerifyCTFacts.scalar {s t : State} (h : VerifyCTFacts s t) : verificationScalar s = verificationScalar t :=
  congrArg Spec.Ed25519.decodeLE h.scalarBytes

theorem VerifyCTFacts.challenge {s t : State} (h : VerifyCTFacts s t) : verificationChallenge s = verificationChallenge t :=
  congrArg Spec.Ed25519.decodeLE h.challengeBytes

theorem verifyRhsPrelude_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) : RelCT isa (VerifySaved s₀ t₀)
    (.seq (.seq (.block (pointTableRead 7680)) (pointFromInput 2 0 64 32)) (.block verifyCombine))
    (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have readct : RelCT isa (VerifySaved s₀ t₀) (.block (pointTableRead 7680)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ hp => regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (hp.1.edi.trans ((h.args 3 (by decide)).trans hp.2.edi.symm)))
  have readwp (u s : State) (hu : VerifyPre u) (hs : Saved u (arg u 3) s) :
      WP isa (.block (pointTableRead 7680)) s (Saved u (arg u 3)) :=
    WP.mono (pointTableRead_ok (hs.ctx hu.scratch.fit hu.scratch.wr) 7680 (by decide) (by decide))
      fun _ k => hs.ikeep hu.scratch.fit (IKeep.of_field k.1)
  have rd := readct.wp (fun s t hp => ⟨readwp s₀ s ps hp.1, readwp t₀ t pt hp.2⟩)
  have mc := pointFromInput_ct h 2 0 64 32 (by decide) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (by decide)
    ps.challenge pt.challenge
  have mw (u s : State) (hu : VerifyPre u) (hs : Saved u (arg u 3) s) :
      WP isa (pointFromInput 2 0 64 32) s (Saved u (arg u 3)) :=
    WP.mono (pointFromInput_ok hu.scratch hu.challenge hs (by decide) (by decide) (by decide)
      (by decide) (by decide)) fun _ k => k.1
  have mm := mc.wp (fun s t hp => ⟨mw s₀ s ps hp.1, mw t₀ t pt hp.2⟩)
  have cc : RelCT isa (VerifySaved s₀ t₀) (.block verifyCombine) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ hp => regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (hp.1.edi.trans ((h.args 3 (by decide)).trans hp.2.edi.symm)))
  exact VG.RelCT.seq (VG.RelCT.seq (rd.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (mm.mono (fun _ _ h => h) (fun _ _ h => h.2))) cc

theorem verifyRhsPrelude_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa (.seq (.seq (.block (pointTableRead 7680)) (pointFromInput 2 0 64 32)) (.block verifyCombine)) s fun t =>
      Saved s₀ (arg s₀ 3) t ∧ point (env t.mem (arg s₀ 3)) 0 1 2 3 = tablePoint s.mem (arg s₀ 3) 7936 ∧
      point (env t.mem (arg s₀ 3)) 4 5 6 7 = Spec.Ed25519.pointAdd (tablePoint s.mem (arg s₀ 3) 7808)
        (Spec.Ed25519.pointMul (verificationChallenge s₀) (tablePoint s.mem (arg s₀ 3) 7680)) := by
  have hc := hs.ctx hp.scratch.fit hp.scratch.wr
  refine WP.seq (WP.seq (WP.mono (pointTableRead_ok hc 7680 (by decide) (by decide)) fun a ⟨ka, pa, _⟩ => ?_))
  have ha := hs.ikeep hp.scratch.fit (IKeep.of_field ka)
  refine WP.mono (pointFromInput_ok hp.scratch hp.challenge ha (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun b ⟨hb, fb, pb, db⟩ => ?_
  have cb := hb.ctx hp.scratch.fit hp.scratch.wr
  refine WP.mono (verifyCombine_ok cb db) fun c ⟨kc, pc, qc⟩ => ?_
  have bt (o : Nat) (ho : 7680 ≤ o) (hn : o + 128 ≤ 8192) :
      tablePoint b.mem (arg s₀ 3) o = tablePoint s.mem (arg s₀ 3) o :=
    (tablePoint_frame hp.scratch.fit fb (by decide) hn (Or.inr ho)).trans
      (field_table_same ka hc o (by omega_using [ho]) hn)
  refine ⟨hb.ikeep hp.scratch.fit (IKeep.of_field kc), ?_, ?_⟩
  · rw [pc, bt 7936 (by decide) (by decide)]
  · rw [qc, pb, pa, bt 7808 (by decide) (by decide)]

def RhsCTPre (s₀ : State) (a r l : Spec.Ed25519.Point) (s : State) : Prop :=
  Saved s₀ (arg s₀ 3) s ∧ tablePoint s.mem (arg s₀ 3) 7680 = a ∧
    tablePoint s.mem (arg s₀ 3) 7808 = r ∧ tablePoint s.mem (arg s₀ 3) 7936 = l

theorem verifyRhs_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a r l : Spec.Ed25519.Point) :
    RelCT isa (fun s t => RhsCTPre s₀ a r l s ∧ RhsCTPre t₀ a r l t) verifyRhs (fun _ _ => True) := by
  have hc := (verifyRhsPrelude_ct h).mono
    (P' := fun (s t : State) => RhsCTPre s₀ a r l s ∧ RhsCTPre t₀ a r l t)
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)
  have hh := ctWithRuns hc (fun _ _ hp => ⟨verifyRhsPrelude_ok (verify_pre h.left) hp.1.1,
    verifyRhsPrelude_ok (verify_pre h.right) hp.2.1⟩)
  rw [verifyRhs]
  apply VG.RelCT.assoc
  apply VG.RelCT.assoc
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (pointEqual_ct (arg s₀ 3) l (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (verificationChallenge s₀) a)))
  intro s t ⟨_, u, v, hp, hs, ht⟩
  have left : EqualCTPre (arg s₀ 3) l (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (verificationChallenge s₀) a)) s := by
    refine ⟨hs.1.ctx (verify_pre h.left).scratch.fit (verify_pre h.left).scratch.wr, ?_, ?_⟩
    · rw [hs.2.1, hp.1.2.2.2]
    · rw [hs.2.2, hp.1.2.1, hp.1.2.2.1]
  have right : EqualCTPre (arg t₀ 3) l (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (verificationChallenge s₀) a)) t := by
    refine ⟨ht.1.ctx (verify_pre h.right).scratch.fit (verify_pre h.right).scratch.wr, ?_, ?_⟩
    · rw [ht.2.1, hp.2.2.2.2]
    · rw [ht.2.2, hp.2.2.1, hp.2.2.2.1, h.challenge]
  exact ⟨left, (h.args 3 (by decide)).symm ▸ right⟩

theorem verifyLhs_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀) verifyLhs (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have base : RelCT isa (VerifySaved s₀ t₀) (.block (constPoint Spec.Ed25519.basePoint)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ hp => regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (hp.1.edi.trans ((h.args 3 (by decide)).trans hp.2.edi.symm)))
  have bw (u s : State) (hu : VerifyPre u) (hs : Saved u (arg u 3) s) :
      WP isa (.block (constPoint Spec.Ed25519.basePoint)) s (Saved u (arg u 3)) :=
    WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) (hs.ctx hu.scratch.fit hu.scratch.wr))
      fun _ k => hs.ikeep hu.scratch.fit (IKeep.of_field k.1)
  have bb := base.wp (fun s t hp => ⟨bw s₀ s ps hp.1, bw t₀ t pt hp.2⟩)
  have mc := pointFromInput_ct h 1 32 32 16 (by decide) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (by decide)
    ps.scalar pt.scalar
  have mw (u s : State) (hu : VerifyPre u) (hs : Saved u (arg u 3) s) :
      WP isa (pointFromInput 1 32 32 16) s (Saved u (arg u 3)) :=
    WP.mono (pointFromInput_ok hu.scratch hu.scalar hs (by decide) (by decide) (by decide)
      (by decide) (by decide)) fun _ k => k.1
  have mm := mc.wp (fun s t hp => ⟨mw s₀ s ps hp.1, mw t₀ t pt hp.2⟩)
  have wc : RelCT isa (VerifySaved s₀ t₀) (.block (pointTableWrite 7936)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ hp => regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (hp.1.edi.trans ((h.args 3 (by decide)).trans hp.2.edi.symm)))
  rw [verifyLhs]
  exact VG.RelCT.seq (bb.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.seq (mm.mono (fun _ _ h => h) (fun _ _ h => h.2)) wc)

def EquationCTPre (s₀ : State) (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  Saved s₀ (arg s₀ 3) s ∧ tablePoint s.mem (arg s₀ 3) 7680 = a ∧ tablePoint s.mem (arg s₀ 3) 7808 = r

theorem verifyEquationPoints_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a r : Spec.Ed25519.Point) :
    RelCT isa (fun s t => EquationCTPre s₀ a r s ∧ EquationCTPre t₀ a r t) verifyEquationPoints (fun _ _ => True) := by
  have hl := (verifyLhs_ct h).mono
    (P' := fun (s t : State) => EquationCTPre s₀ a r s ∧ EquationCTPre t₀ a r t)
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)
  have hh := ctWithRuns hl (fun _ _ hp => ⟨verifyLhs_ok (verify_pre h.left) hp.1.1,
    verifyLhs_ok (verify_pre h.right) hp.2.1⟩)
  rw [verifyEquationPoints]
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (verifyRhs_ct h a r (Spec.Ed25519.pointMul (verificationScalar s₀) Spec.Ed25519.basePoint))
  intro s t ⟨_, u, v, hp, hs, ht⟩
  refine ⟨⟨hs.1, hs.2.2.1.trans hp.1.2.1, hs.2.2.2.trans hp.1.2.2, hs.2.1⟩,
    ⟨ht.1, ht.2.2.1.trans hp.2.2.1, ht.2.2.2.trans hp.2.2.2, ?_⟩⟩
  rw [ht.2.1, h.scalar]

end VG.Proof.Ed25519.X86

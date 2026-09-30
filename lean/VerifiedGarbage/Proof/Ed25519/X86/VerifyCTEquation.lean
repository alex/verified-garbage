import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTMultiply
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.X86.PointEqualCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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

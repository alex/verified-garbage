import VerifiedGarbage.Proof.Ed25519.X86.DecodedThenCT
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTEquation

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

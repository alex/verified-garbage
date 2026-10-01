import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTDecodeR

/-! Untrusted: decoding the public key selects the public verification continuation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 Edwards

theorem verifyStoreA_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a : Spec.Ed25519.Point) {Aa : EPoint dZ} (hA : Rep a Aa) :
    RelCT isa (fun s t => (VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      point (env s.mem base) 0 1 2 3 = a) ∧ (VerifyPublic base pk sig challenge pkbs rbs sbs kbs t ∧
      point (env t.mem base) 0 1 2 3 = a))
      (.seq (.block (pointTableWrite 7424)) verifyDecodeR) (fun _ _ => True) := by
  have ht := (pointTableWrite_ct base 7424 (by decide)).mono
    (fun s t (h : (VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      point (env s.mem base) 0 1 2 3 = a) ∧ (VerifyPublic base pk sig challenge pkbs rbs sbs kbs t ∧
      point (env t.mem base) 0 1 2 3 = a)) => ⟨h.1.1.context.scratch.rdi, h.2.1.context.scratch.rdi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      point (env s.mem base) 0 1 2 3 = a) :
      WP isa (.block (pointTableWrite 7424)) s (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a) := by
    refine WP.mono (pointTableWrite_ok h.1.context.scratch 7424 (by decide) (by decide)) fun t ⟨kt, tv, _⟩ => ?_
    exact ⟨h.1.of_keep (kt.mono (by decide) (by decide)), tv.trans h.2⟩
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (verifyDecodeR_ct base pk sig challenge pkbs rbs sbs kbs a hA)

theorem verifyDecodeA_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    RelCT isa (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs t) verifyDecodeA (fun _ _ => True) := by
  let P := VerifyPublic base pk sig challenge pkbs rbs sbs kbs
  have loadCT : RelCT isa (fun s t => P s ∧ P t)
      (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7936))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
    exact fun _ _ h => rdi_agree h.1.context.scratch.rdi h.2.context.scratch.rdi
  have loadWP (s : State) (h : P s) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7936))]) s fun t =>
        P t ∧ DecodeCTPre base pk pkbs t := by
    refine WP.mono (loadPointer_ok h.context.scratch .rdx 7936 (by decide)) fun t ⟨tp, kt⟩ => ?_
    have kp : VerifyKeep base s t := PowersKeep.of_keeps kt (by decide)
    have hp := h.of_keep kp
    exact ⟨hp, hp.context.scratch, tp.trans h.context.pkHeader, hp.context.pkRead, hp.pkBytes⟩
  have hl := VG.RelCT.wp loadCT (fun s t h => ⟨loadWP s h.1, loadWP t h.2⟩)
  have decodeCT := (pointDecode_ct base pk pkbs).mono
    (fun s t (h : (P s ∧ DecodeCTPre base pk pkbs s) ∧ (P t ∧ DecodeCTPre base pk pkbs t)) =>
      ⟨h.1.2, h.2.2⟩) (fun _ _ h => h)
  have decodeWP (s : State) (h : P s ∧ DecodeCTPre base pk pkbs s) :
      WP isa pointDecode s fun t => P t ∧ DecodeResult base (Spec.Ed25519.decodePoint pkbs) t := by
    have hd := pointDecode_ok (base := base) (p := pk) h.2.1 h.2.2.1 h.2.2.2.1
    rw [h.2.2.2.2] at hd
    with_reducible apply WP.mono hd
    intro t ht
    exact ⟨h.1.of_keep (PowersKeep.of_decode ht.1), ht.2⟩
  have hd := VG.RelCT.wp decodeCT (fun s t h => ⟨decodeWP s h.1, decodeWP t h.2⟩)
  rw [verifyDecodeA]
  refine VG.RelCT.seq (hl.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.seq (hd.mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_)
  apply decodedThen_ct base (Spec.Ed25519.decodePoint pkbs) P _
  · intro s t kt h
    exact h.of_keep (PowersKeep.of_keeps kt (by simp))
  · intro a ha
    obtain ⟨Aa, hA⟩ := decodePoint_rep ha
    exact verifyStoreA_ct base pk sig challenge pkbs rbs sbs kbs a hA

end VG.Proof.Ed25519.X86_64

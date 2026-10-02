import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTPublic
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodedThenCT

/-! Untrusted: decoding R and selecting the public equation continuation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 Edwards

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

def DecodeRCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧ tablePoint s.mem base 7424 = a

theorem verifyStoreR_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    RelCT isa (fun s t => (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      point (env s.mem base) 0 1 2 3 = r) ∧ (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a t ∧
      point (env t.mem base) 0 1 2 3 = r))
      (.seq (.block (pointTableWrite 7552)) (verifyEquationPoints fld dbl)) (fun _ _ => True) := by
  have ht := (pointTableWrite_ct base 7552 (by decide)).mono
    (fun s t (h : (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      point (env s.mem base) 0 1 2 3 = r) ∧ (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a t ∧
      point (env t.mem base) 0 1 2 3 = r)) => ⟨h.1.1.1.context.scratch.rdi, h.2.1.1.context.scratch.rdi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      point (env s.mem base) 0 1 2 3 = r) :
      WP isa (.block (pointTableWrite 7552)) s (PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r) := by
    refine WP.mono (pointTableWrite_ok h.1.1.context.scratch 7552 (by decide) (by decide)) fun t ⟨kt, tv, _⟩ => ?_
    refine ⟨h.1.1.of_keep (kt.mono (by decide) (by decide)), ?_, tv.trans h.2⟩
    exact (kt.mem.point (by decide) (Or.inl (by decide)) (by decide)).trans h.1.2
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (verifyEquationPoints_ct base pk sig challenge pkbs rbs sbs kbs a r hA hR)

theorem verifyDecodeR_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a : Spec.Ed25519.Point) {Aa : EPoint dZ} (hA : Rep a Aa) :
    RelCT isa (fun s t => DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a t) (verifyDecodeR fld dbl) (fun _ _ => True) := by
  let P := DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a
  have loadCT : RelCT isa (fun s t => P s ∧ P t)
      (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944))]) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.context.scratch.rdi h.2.1.context.scratch.rdi
  have loadWP (s : State) (h : P s) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944))]) s fun t =>
        P t ∧ DecodeCTPre base sig rbs t := by
    refine WP.mono (loadPointer_ok h.1.context.scratch .rdx 7944 (by decide)) fun t ⟨tp, kt⟩ => ?_
    have kp : VerifyKeep base s t := PowersKeep.of_keeps kt (by decide)
    have hp := h.1.of_keep kp
    exact ⟨⟨hp, by rw [kt.2.1]; exact h.2⟩,
      hp.context.scratch, tp.trans h.1.context.sigHeader, hp.context.rRead, hp.rBytes⟩
  have hl := VG.RelCT.wp loadCT (fun s t h => ⟨loadWP s h.1, loadWP t h.2⟩)
  have decodeCT := (pointDecode_ct (fld := fld) base sig rbs).mono
    (fun s t (h : (P s ∧ DecodeCTPre base sig rbs s) ∧ (P t ∧ DecodeCTPre base sig rbs t)) =>
      ⟨h.1.2, h.2.2⟩) (fun _ _ h => h)
  have decodeWP (s : State) (h : P s ∧ DecodeCTPre base sig rbs s) :
      WP isa (pointDecode fld) s fun t => P t ∧ DecodeResult base (Spec.Ed25519.decodePoint rbs) t := by
    have hd := pointDecode_ok (fld := fld) (base := base) (p := sig) h.2.1 h.2.2.1 h.2.2.2.1
    rw [h.2.2.2.2] at hd
    with_reducible apply WP.mono hd
    intro t ht
    have kt := ht.1
    exact ⟨⟨h.1.1.of_keep (PowersKeep.of_decode kt),
      (workspace_tablePoint kt.mem (by decide) (by decide)).trans h.1.2⟩, ht.2⟩
  have hd := VG.RelCT.wp decodeCT (fun s t h => ⟨decodeWP s h.1, decodeWP t h.2⟩)
  rw [verifyDecodeR]
  refine VG.RelCT.seq (hl.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.seq (hd.mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_)
  apply decodedThen_ct base (Spec.Ed25519.decodePoint rbs) P _
  · intro s t kt h
    exact ⟨h.1.of_keep (PowersKeep.of_keeps kt (by simp)), by rw [kt.2.1]; exact h.2⟩
  · intro r hr
    obtain ⟨Ra, hR⟩ := decodePoint_rep hr
    exact verifyStoreR_ct base pk sig challenge pkbs rbs sbs kbs a r hA hR

end VG.Proof.Ed25519.X86_64

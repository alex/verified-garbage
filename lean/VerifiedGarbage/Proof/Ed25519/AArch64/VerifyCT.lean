import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTBody
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMain

/-! Complete verification leaks only the inputs declared public by its contract. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

open VG.Spec.Ed25519 (bytesAt)

theorem VerifyStarted.public {s t : State} (hs : verifyLocal.pre s) (h : VerifyStarted s t) :
    VerifyPublic (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
      (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 32)
      (bytesAt s.mem (off (s.gpr .x1) 32) 32) (bytesAt s.mem (s.gpr .x2) 64) t := by
  have hm := verifyBytes_frame h.frame hs.2.2.2.1 (by decide)
  have hr := congrArg (List.take 32) hm
  have hscalar := congrArg (List.drop 32) hm
  rw [signatureBytes_take, signatureBytes_take] at hr
  rw [signatureBytes_drop, signatureBytes_drop] at hscalar
  exact ⟨h.context, verifyBytes_frame h.frame hs.2.2.1 (by decide), hr, hscalar,
    verifyBytes_frame h.frame hs.2.2.2.2.1 (by decide)⟩

theorem VerifyStarted.public_right {s u t : State} (hu : verifyLocal.pre u)
    (hp : verifyLocal.pub s u) (h : VerifyStarted u t) :
    VerifyPublic (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
      (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 32)
      (bytesAt s.mem (off (s.gpr .x1) 32) 32) (bytesAt s.mem (s.gpr .x2) 64) t := by
  have ht := h.public hu
  obtain ⟨_, pk, sig, challenge, base, pbs, sigbs, kbs⟩ := hp
  have rbs := congrArg (List.take 32) sigbs
  have sbs := congrArg (List.drop 32) sigbs
  rw [signatureBytes_take, signatureBytes_take] at rbs
  rw [signatureBytes_drop, signatureBytes_drop] at sbs
  rw [← pbs, ← rbs, ← sbs, ← kbs, ← pk, ← sig, ← challenge, ← base] at ht
  exact ht

theorem verifyFinish_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (([mov .x2 .x0, mov .x0 .x8] : List Instr) ++ scalarRestore)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem verifyBody_base_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    CT (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs t)
      (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid))
      (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base) := by
  have hw (s : State) (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs s) :
      WP isa (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid)) s
        (fun t => t.gpr .x0 = base) :=
    WP.mono (verifyBody_ok h.context) fun _ kt => (kt.1.scratch h.context.scratch).x0
  exact (CT.wp (verifyBody_ct base pk sig challenge pkbs rbs sbs kbs)
    (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  have setupCT : CT (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      (.block verifySetup) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x3]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.2.2.2.2.2.2.1
  have hp := withRuns setupCT (fun s t h => ⟨verifySetup_state_ok h.1, verifySetup_state_ok h.2.1⟩)
  have whole : CT (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      verifyEquation (fun _ _ => True) := by
    rw [verifyEquation]
    refine CT.seq hp ?_
    intro s t ts tt s' t' ⟨hsp, _, a, b, hab, ha, hb⟩ es et
    have pa := ha.public hab.1
    have pb := hb.public_right hab.2.1 hab.2.2
    exact CT.seq
      (verifyBody_base_ct (a.gpr .x3) (a.gpr .x0) (a.gpr .x1) (a.gpr .x2)
        (bytesAt a.mem (a.gpr .x0) 32) (bytesAt a.mem (a.gpr .x1) 32)
        (bytesAt a.mem (off (a.gpr .x1) 32) 32) (bytesAt a.mem (a.gpr .x2) 64))
      (verifyFinish_ct (a.gpr .x3)) _ _ _ _ _ _ ⟨hsp, pa, pb⟩ es et
  intro s t ts tt s' t' hs ht hp es et
  exact (whole _ _ _ _ _ _ ⟨hp.1, hs, ht, hp⟩ es et).1

end VG.Proof.Ed25519.AArch64

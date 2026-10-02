import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTBody
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMain

/-! Untrusted: complete verification leaks only the inputs declared public by its contract. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)
open VG.Spec.Ed25519 (bytesAt)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

theorem VerifyStarted.public {s t : State} (hs : verifyLocal.pre s) (h : VerifyStarted s t) :
    VerifyPublic (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
      (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 32)
      (bytesAt s.mem (off (s.gpr .rsi) 32) 32) (bytesAt s.mem (s.gpr .rdx) 64) t := by
  have hm := verifyBytes_frame h.frame hs.2.2.2.1 (by decide)
  have hr := congrArg (List.take 32) hm
  have hscalar := congrArg (List.drop 32) hm
  rw [signatureBytes_take, signatureBytes_take] at hr
  rw [signatureBytes_drop, signatureBytes_drop] at hscalar
  exact ⟨h.context, verifyBytes_frame h.frame hs.2.2.1 (by decide), hr, hscalar,
    verifyBytes_frame h.frame hs.2.2.2.2.1 (by decide)⟩

theorem VerifyStarted.public_right {s u t : State} (hu : verifyLocal.pre u)
    (hp : verifyLocal.pub s u) (h : VerifyStarted u t) :
    VerifyPublic (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
      (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 32)
      (bytesAt s.mem (off (s.gpr .rsi) 32) 32) (bytesAt s.mem (s.gpr .rdx) 64) t := by
  have ht := h.public hu
  obtain ⟨_, pk, sig, challenge, base, pbs, sigbs, kbs⟩ := hp
  have rbs := congrArg (List.take 32) sigbs
  have sbs := congrArg (List.drop 32) sigbs
  rw [signatureBytes_take, signatureBytes_take] at rbs
  rw [signatureBytes_drop, signatureBytes_drop] at sbs
  rw [← pbs, ← rbs, ← sbs, ← kbs, ← pk, ← sig, ← challenge, ← base] at ht
  exact ht

theorem verifyFinish_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ scalarRestore)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem verifyBody_rdi_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    RelCT isa (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs t)
      (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld dbl) recoverInvalid))
      (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) := by
  have hw (s : State) (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs s) :
      WP isa (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld dbl) recoverInvalid)) s
        (fun t => t.gpr .rdi = base) :=
    WP.mono (verifyBody_ok h.context) fun _ kt => (kt.1.scratch h.context.scratch).rdi
  exact (VG.RelCT.wp (verifyBody_ct base pk sig challenge pkbs rbs sbs kbs)
    (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub (verifyEquation fld dbl) := by
  have setupCT : RelCT isa (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      (.block verifySetup) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rcx]) _ (by fld_taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.2.2.2.2.2.2.1
  have hp := withRuns setupCT (fun s t h => ⟨verifySetup_state_ok h.1, verifySetup_state_ok h.2.1⟩)
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  rw [verifyEquation]
  refine VG.RelCT.seq hp ?_
  intro s t ts tt s' t' ⟨_, a, b, hab, ha, hb⟩ es et
  have pa := ha.public hab.1
  have pb := hb.public_right hab.2.1 hab.2.2
  exact VG.RelCT.seq
    (verifyBody_rdi_ct (a.gpr .rcx) (a.gpr .rdi) (a.gpr .rsi) (a.gpr .rdx)
      (bytesAt a.mem (a.gpr .rdi) 32) (bytesAt a.mem (a.gpr .rsi) 32)
      (bytesAt a.mem (off (a.gpr .rsi) 32) 32) (bytesAt a.mem (a.gpr .rdx) 64))
    (verifyFinish_ct (a.gpr .rcx)) _ _ _ _ _ _ ⟨pa, pb⟩ es et

end VG.Proof.Ed25519.X86_64

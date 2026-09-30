import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTRoot

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

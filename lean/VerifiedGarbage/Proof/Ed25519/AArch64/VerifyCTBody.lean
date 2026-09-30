import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTDecodeA

/-! Untrusted: the canonical scalar check depends only on the public signature. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


theorem verifyScalar_ct (base pk sig challenge : Addr) :
    CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block verifyScalar) (fun _ _ => True) := by
  have ht : CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0])
      (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.scratch.x0 h.2.scratch.x0
  have hw (s : State) (h : VerifyContext s base pk sig challenge) :
      WP isa (.block [ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0]) s
        (fun t => t.gpr .x2 = off sig 32) := by
    change WP isa (.block (([ld .x2 7944] : List Instr) ++
      ([.addImm .x .x2 .x2 32] : List Instr) ++ ([.movz .w .x10 0 0] : List Instr))) s _
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (loadPointer_ok h.scratch .x2 7944 (by decide) (by decide)) fun a ⟨ap, _⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (add32_ok a .x2) fun b ⟨bp, _⟩ => ?_
    refine WP.mono (setZeroX10_ok b) fun t ⟨_, kt⟩ => ?_
    have tp := (kt.gpr .x2 (by decide)).trans bp
    rw [tp, ap, h.sigHeader]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have tailCT : CT (fun s t => s.gpr .x2 = off sig 32 ∧ t.gpr .x2 = off sig 32)
      (.block (loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr))) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x2]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.1.trans h.2.symm
  change CT _ (.block (([ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0] : List Instr) ++
    (loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr)))) _
  exact blockAppend_ct (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) tailCT

theorem verifyBody_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    CT (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs t)
      (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid)) (fun _ _ => True) := by
  let P := VerifyPublic base pk sig challenge pkbs rbs sbs kbs
  have ht := (verifyScalar_ct base pk sig challenge).mono
    (fun _ _ (h : P _ ∧ P _) => ⟨h.1.context, h.2.context⟩) (fun _ _ h => h)
  have hw (s : State) (h : P s) : WP isa (.block verifyScalar) s fun t =>
      P t ∧ eval (.nonzero .x .x8) t = some (decide (Spec.Ed25519.decodeLE sbs < Spec.Ed25519.L)) := by
    refine WP.mono (verifyScalar_ok h.context.scratch h.context.sigHeader h.context.scalarRead) fun t ⟨kt, _, tc⟩ => ?_
    exact ⟨h.of_keep (PowersKeep.of_keep kt), by change some (t.gpr .x8 != 0) = _; rw [tc, h.sBytes]⟩
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (verifyDecodeA_ct base pk sig challenge pkbs rbs sbs kbs).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64

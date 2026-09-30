import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTDecodeA

/-! Untrusted: the canonical scalar check depends only on the public signature. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

theorem verifyScalar_ct (base pk sig challenge : Addr) :
    RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block verifyScalar) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944)), .alu .add .rdx (.imm 32)])
      (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
    exact fun _ _ h => rdi_agree h.1.scratch.rdi h.2.scratch.rdi
  have hw (s : State) (h : VerifyContext s base pk sig challenge) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944)), .alu .add .rdx (.imm 32)]) s
        (fun t => t.gpr .rdx = off sig 32) := by
    change WP isa (.block (([.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944))] : List Instr) ++
      [.alu .add .rdx (.imm 32)])) s _
    rw [WP.block_append_iff]
    refine WP.mono (loadPointer_ok h.scratch .rdx 7944 (by decide)) fun a ⟨ap, _⟩ => ?_
    refine WP.mono (add32_ok a .rdx) fun t ⟨tp, _⟩ => ?_
    rw [tp, ap, h.sigHeader]
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have tailCT : RelCT isa (fun s t => s.gpr .rdx = off sig 32 ∧ t.gpr .rdx = off sig 32)
      (.block (loadScalarWords ++ scalarSubtract)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdx]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.1.trans h.2.symm
  rw [verifyScalar, List.append_assoc]
  exact blockAppend_ct (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) tailCT

theorem verifyBody_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    RelCT isa (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs t)
      (.seq (.block verifyScalar) (.ite .b verifyDecodeA recoverInvalid)) (fun _ _ => True) := by
  let P := VerifyPublic base pk sig challenge pkbs rbs sbs kbs
  have ht := (verifyScalar_ct base pk sig challenge).mono
    (fun _ _ (h : P _ ∧ P _) => ⟨h.1.context, h.2.context⟩) (fun _ _ h => h)
  have hw (s : State) (h : P s) : WP isa (.block verifyScalar) s fun t =>
      P t ∧ t.cf = some (decide (Spec.Ed25519.decodeLE sbs < Spec.Ed25519.L)) := by
    refine WP.mono (verifyScalar_ok h.context.scratch h.context.sigHeader h.context.scalarRead) fun t ⟨kt, _, tc⟩ => ?_
    exact ⟨h.of_keep (PowersKeep.of_keep kt), by rw [tc, h.sBytes]⟩
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (verifyDecodeA_ct base pk sig challenge pkbs rbs sbs kbs).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64

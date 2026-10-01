import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTInputs
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulVarBatchCT

/-! Untrusted: scalar multiplication and its surrounding fixed-address table operations. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem pointTableWrite_ct (base : Addr) (o : Nat) (ho : o ∈ [7424, 7552, 7680]) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (pointTableWrite o)) (fun _ _ => True) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  all_goals
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1 h.2

theorem verifyReadA_ct (base k : Addr) :
    CT (fun s t => ScalarCTPre 32 base k s ∧ ScalarCTPre 32 base k t)
      (.block (pointTableRead 7424))
      (fun s t => ScalarCTPre 32 base k s ∧ ScalarCTPre 32 base k t) := by
  have ht : CT (fun s t => ScalarCTPre 32 base k s ∧ ScalarCTPre 32 base k t)
      (.block (pointTableRead 7424)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : ScalarCTPre 32 base k s) :
      WP isa (.block (pointTableRead 7424)) s (ScalarCTPre 32 base k) :=
    WP.mono (pointTableRead_ok h.1 7424 (by decide) (by decide)) fun _ kt => h.of_counter kt.1
  exact (CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem verifyCombine_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block verifyCombine) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem verifyLoadScalar_ok {s : State} {base pk sig challenge : Addr} {sc : Nat}
    (h : VerifyContext s base pk sig challenge ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32) = sc) :
    WP isa (.block [ld .x1 7944, .addImm .x .x1 .x1 32]) s
      (ScalarVarCTPre 16 base (off sig 32) sc) := by
  change WP isa (.block (([ld .x1 7944] : List Instr) ++
    ([.addImm .x .x1 .x1 32] : List Instr))) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok h.1.scratch .x1 7944 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_
  refine WP.mono (add32_ok a .x1) fun t ⟨tp, kt⟩ => ?_
  refine ⟨⟨(h.1.scratch.of_keeps ka (by decide)).of_keeps kt (by decide), ?_, ?_, h.1.scalarFar⟩, ?_⟩
  · rw [tp, ap, h.1.sigHeader]
  · intro i hi; rw [kt.rd, kt.wr, ka.rd, ka.wr]; exact h.1.scalarBytes i hi
  · rw [kt.mem, ka.mem]; exact h.2

theorem verifyLhs_ct (base pk sig challenge : Addr) (sc : Nat) :
    CT (fun s t => (VerifyContext s base pk sig challenge ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32) = sc) ∧
      (VerifyContext t base pk sig challenge ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (off sig 32) 32) = sc))
      verifyLhs (fun _ _ => True) := by
  rw [verifyLhs]
  refine seq_runs ?_ (fun x h => verifyLoadScalar_ok h) (fun y h => verifyLoadScalar_ok h) ?_
  · exact (verifyLoadScalar_ct base pk sig challenge).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
      (fun _ _ _ => trivial)
  have hm (s : State) (h : ScalarVarCTPre 16 base (off sig 32) sc s) :
      WP isa baseFromScalarVar s fun t => t.gpr .x0 = base :=
    WP.mono (baseFromScalarVar_ok h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2) fun _ kt => (kt.1.scratch h.1.1).x0
  refine seq_runs (baseFromScalarVar_ct base (off sig 32) sc) (fun x h => hm x h) (fun y h => hm y h) ?_
  exact pointTableWrite_ct base 7680 (by decide)

end VG.Proof.Ed25519.AArch64

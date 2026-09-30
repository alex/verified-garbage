import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTInputs

/-! Untrusted: scalar multiplication and its surrounding fixed-address table operations. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

theorem verifyBasePoint_ct (base k : Addr) :
    RelCT isa (fun s t => ScalarCTPre 16 base k s ∧ ScalarCTPre 16 base k t)
      (.block (constPoint Spec.Ed25519.basePoint))
      (fun s t => ScalarCTPre 16 base k s ∧ ScalarCTPre 16 base k t) := by
  have ht : RelCT isa (fun s t => ScalarCTPre 16 base k s ∧ ScalarCTPre 16 base k t)
      (.block (constPoint Spec.Ed25519.basePoint)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : ScalarCTPre 16 base k s) :
      WP isa (.block (constPoint Spec.Ed25519.basePoint)) s (ScalarCTPre 16 base k) :=
    WP.mono (fieldCodeWide_ok h.1 (constPointOps Spec.Ed25519.basePoint)) fun _ kt => h.of_keep kt.1
  exact (VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem scalarTrace_rdi (count : Nat) (base k : Addr) (hn0 : 0 < count) (hn : count ≤ 32)
    (ht : RelCT isa (fun s t => ScalarCTPre count base k s ∧ ScalarCTPre count base k t)
      (pointFromScalar count) (fun _ _ => True)) :
    RelCT isa (fun s t => ScalarCTPre count base k s ∧ ScalarCTPre count base k t)
      (pointFromScalar count) (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) := by
  have hw (s : State) (h : ScalarCTPre count base k s) :
      WP isa (pointFromScalar count) s fun t => t.gpr .rdi = base :=
    WP.mono (pointFromScalar_ok h.1 h.2.1 count hn0 hn h.2.2.1 h.2.2.2)
      fun _ kt => (kt.1.scratch h.1).rdi
  exact (VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem pointTableWrite_ct (base : Addr) (o : Nat) (ho : o ∈ [7424, 7552, 7680]) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (pointTableWrite o)) (fun _ _ => True) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  all_goals
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
    exact fun _ _ h => rdi_agree h.1 h.2

theorem verifyReadA_ct (base k : Addr) :
    RelCT isa (fun s t => ScalarCTPre 32 base k s ∧ ScalarCTPre 32 base k t)
      (.block (pointTableRead 7424))
      (fun s t => ScalarCTPre 32 base k s ∧ ScalarCTPre 32 base k t) := by
  have ht : RelCT isa (fun s t => ScalarCTPre 32 base k s ∧ ScalarCTPre 32 base k t)
      (.block (pointTableRead 7424)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : ScalarCTPre 32 base k s) :
      WP isa (.block (pointTableRead 7424)) s (ScalarCTPre 32 base k) :=
    WP.mono (pointTableRead_ok h.1 7424 (by decide) (by decide)) fun _ kt => h.of_rbx kt.1
  exact (VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem verifyCombine_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block verifyCombine) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem verifyLhs_ct (base pk sig challenge : Addr) :
    RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      verifyLhs (fun _ _ => True) := by
  rw [verifyLhs]
  exact VG.RelCT.seq (verifyLoadScalar_ct base pk sig challenge)
    (VG.RelCT.seq (verifyBasePoint_ct base (off sig 32))
      (VG.RelCT.seq (scalarTrace_rdi 16 base (off sig 32) (by decide) (by decide)
        (pointFromScalar16_ct base (off sig 32))) (pointTableWrite_ct base 7680 (by decide))))

end VG.Proof.Ed25519.X86_64

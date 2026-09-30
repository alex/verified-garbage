import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTInputs

/-! Untrusted: scalar multiplication and its surrounding fixed-address table operations. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem verifyBasePoint_ct (base k : Addr) :
    CT (fun s t => ScalarCTPre 16 base k s ∧ ScalarCTPre 16 base k t)
      (.block (constPoint Spec.Ed25519.basePoint))
      (fun s t => ScalarCTPre 16 base k s ∧ ScalarCTPre 16 base k t) := by
  have ht : CT (fun s t => ScalarCTPre 16 base k s ∧ ScalarCTPre 16 base k t)
      (.block (constPoint Spec.Ed25519.basePoint)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : ScalarCTPre 16 base k s) :
      WP isa (.block (constPoint Spec.Ed25519.basePoint)) s (ScalarCTPre 16 base k) :=
    WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) h.1) fun _ kt => h.of_keep kt.1
  exact (CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem scalarTrace_base (count : Nat) (base k : Addr) (hn0 : 0 < count) (hn : count ≤ 32)
    (ht : CT (fun s t => ScalarCTPre count base k s ∧ ScalarCTPre count base k t)
      (pointFromScalar count) (fun _ _ => True)) :
    CT (fun s t => ScalarCTPre count base k s ∧ ScalarCTPre count base k t)
      (pointFromScalar count) (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base) := by
  have hw (s : State) (h : ScalarCTPre count base k s) :
      WP isa (pointFromScalar count) s fun t => t.gpr .x0 = base :=
    WP.mono (pointFromScalar_ok h.1 h.2.1 count hn0 hn h.2.2.1 h.2.2.2)
      fun _ kt => (kt.1.scratch h.1).x0
  exact (CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

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

theorem verifyLhs_ct (base pk sig challenge : Addr) :
    CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      verifyLhs (fun _ _ => True) := by
  rw [verifyLhs]
  exact CT.seq (verifyLoadScalar_ct base pk sig challenge)
    (CT.seq (verifyBasePoint_ct base (off sig 32))
      (CT.seq (scalarTrace_base 16 base (off sig 32) (by decide) (by decide)
        (pointFromScalar16_ct base (off sig 32))) (pointTableWrite_ct base 7680 (by decide))))

end VG.Proof.Ed25519.AArch64

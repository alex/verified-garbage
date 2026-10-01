import VerifiedGarbage.Proof.Ed25519.X86_64.BaseMultiplyPrecomputed
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCT
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedLit

/-! The precomputed initialization and original scalar loop have a public trace. -/
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64

theorem baseMultiplyPrecomputed_ct (base : Addr) (scalar₁ scalar₂ : Nat) :
    RelCT isa (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      baseMultiplyPrecomputed (fun _ _ => True) := by
  have initCT : RelCT isa (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      baseMultiplyPrecomputedInit (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  have hi := withRuns initCT (fun x y h =>
    ⟨baseMultiplyPrecomputedInit_ok h.1.1 scalar₁ h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     baseMultiplyPrecomputedInit_ok h.2.1 scalar₂ h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [baseMultiplyPrecomputed]
  refine VG.RelCT.seq hi ?_
  intro x y tx ty x' y' ⟨_, a, b, _, hx, hy⟩ ex ey
  exact pointMulLoop_ct a b base 16 scalar₁ scalar₂ _ _ (by decide) 16 _ _ _ _ _ _ ⟨hx, hy⟩ ex ey

end VG.Proof.Ed25519.X86_64

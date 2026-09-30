import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCT
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit

/-! Untrusted: constant-time multiplication by the entire 512-bit challenge. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

theorem pointMultiply32_ct (base : Addr) (scalar₁ scalar₂ : Nat) :
    RelCT isa (fun x y => MulCTPreN 32 base scalar₁ x ∧ MulCTPreN 32 base scalar₂ y)
      (pointMultiply 32) (fun _ _ => True) := by
  apply pointMultiply_ct_of_init 32 base scalar₁ scalar₂ (by decide) (by decide)
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm

end VG.Proof.Ed25519.X86_64

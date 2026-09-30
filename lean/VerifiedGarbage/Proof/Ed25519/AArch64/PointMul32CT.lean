import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCT
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit

/-! Untrusted: constant-time multiplication by the entire 512-bit challenge. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem pointMultiply32_ct (base : Addr) (scalar₁ scalar₂ : Nat) :
    CT (fun x y => MulCTPreN 32 base scalar₁ x ∧ MulCTPreN 32 base scalar₂ y)
      (pointMultiply 32) (fun _ _ => True) := by
  apply pointMultiply_ct_of_init 32 base scalar₁ scalar₂ (by decide) (by decide)
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact h.1.1.x0.trans h.2.1.x0.symm

end VG.Proof.Ed25519.AArch64

import VerifiedGarbage.Proof.Gcm.X86.GhashCT
import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashX86.pre
    Proof.Gcm.ghashX86.pub Impl.Gcm.X86.Pclmul.ghash :=
  VG.Taint.constantTime (A := sseTaint) Proof.Gcm.X86.ghτ₀
    (fun _ _ h₁ h₂ hp => Proof.Gcm.X86.gh_agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Gcm.X86.Pclmul

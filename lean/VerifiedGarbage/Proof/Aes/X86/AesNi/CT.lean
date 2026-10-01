import VerifiedGarbage.Proof.Aes.X86.ExpandKeyCT
import VerifiedGarbage.Proof.Aes.X86.Ctr32CT
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint

namespace VG.Proof.Aes.X86.AesNi
open VG.X86

theorem expandKey_ct : ConstantTime isa Proof.Aes.expandKeyX86.pre
    Proof.Aes.expandKeyX86.pub Impl.Aes.X86.AesNi.expandKey :=
  VG.Taint.constantTime (A := sseTaint) Proof.Aes.X86.ekτ₀
    (fun _ _ h₁ h₂ hp => Proof.Aes.X86.ek_agree₀ h₁ h₂ hp) (by taint_decide)

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32X86.pre
    Proof.Aes.ctr32X86.pub Impl.Aes.X86.AesNi.ctr32 :=
  VG.Taint.constantTime (A := sseTaint) Proof.Aes.X86.ctrτ₀
    (fun _ _ h₁ h₂ hp => Proof.Aes.X86.ctr_agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Aes.X86.AesNi

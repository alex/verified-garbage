import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.X86_64.ConstantTime

/-! # Constant-time CBC callers -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.Impl.Rc2.X86_64.Cbc

theorem encrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

theorem decrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

end VG.Proof.Rc2.X86_64.Cbc

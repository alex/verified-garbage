import VerifiedGarbage.Proof.Rc2.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! # Constant-time RC2 block operations -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem encryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2]) encryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem decryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r0, .r1, .r2]) decryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

end VG.Proof.Rc2.Arm

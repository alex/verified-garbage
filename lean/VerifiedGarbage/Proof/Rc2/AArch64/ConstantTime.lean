import VerifiedGarbage.Proof.Rc2.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! # Constant-time RC2 block and key-expansion programs -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

/-- Only argument pointers and explicitly public integer parameters agree;
all memory contents, including the key, schedule, and data, may differ. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem encryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2]) encryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem decryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2]) decryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3, .x4]) expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.Rc2.AArch64

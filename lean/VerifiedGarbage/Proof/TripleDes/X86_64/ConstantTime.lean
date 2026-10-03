import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
import VerifiedGarbage.Proof.Framework.X86_64.Taint

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

def blockTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx], flags := false,
    lens := [0, 512], bases := [(.rdx, 1, 0)] }

theorem encryptBlock_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree blockTaint s t) :
    ConstantTime isa pre pub encryptBlock :=
  VG.Taint.constantTime (A := taint) blockTaint hagree (by taint_decide)

theorem decryptBlock_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree blockTaint s t) :
    ConstantTime isa pre pub decryptBlock :=
  VG.Taint.constantTime (A := taint) blockTaint hagree (by taint_decide)

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi, .rdx, .rcx]) Key.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

end VG.Proof.TripleDes.X86_64

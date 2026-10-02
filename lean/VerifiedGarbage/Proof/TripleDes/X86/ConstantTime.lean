import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
import VerifiedGarbage.Proof.Framework.X86.Taint

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Impl.TripleDes.X86

def blockTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8, 512],
    argLen := 16, argBases := [(8, 0), (12, 1)] }
def keyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [384, 512],
    argLen := 20, argBases := [(12, 0), (16, 1)] }
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 1024],
    argLen := 20, argBases := [(8, 0), (16, 1)], room := 16 }

theorem encryptBlock_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree blockTaint s₁ s₂) :
    ConstantTime isa pre pub encryptBlock :=
  VG.Taint.constantTime (A := taint) blockTaint h (by taint_decide)

theorem decryptBlock_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree blockTaint s₁ s₂) :
    ConstantTime isa pre pub decryptBlock :=
  VG.Taint.constantTime (A := taint) blockTaint h (by taint_decide)

theorem expandKey_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree keyTaint s₁ s₂) :
    ConstantTime isa pre pub Key.expandKey :=
  VG.Taint.constantTime (A := taint) keyTaint h (by taint_decide)

theorem ecbEncrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree ecbTaint s₁ s₂) :
    ConstantTime isa pre pub Ecb.encrypt :=
  VG.Taint.constantTime (A := taint) ecbTaint h (by taint_decide)

theorem ecbDecrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree ecbTaint s₁ s₂) :
    ConstantTime isa pre pub Ecb.decrypt :=
  VG.Taint.constantTime (A := taint) ecbTaint h (by taint_decide)

end VG.Proof.TripleDes.X86

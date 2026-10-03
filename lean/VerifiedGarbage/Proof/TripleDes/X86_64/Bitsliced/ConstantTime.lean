import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Constant time

The pointers, the count of blocks and the stack pointer are public; so is
everything the function computes from them (the batches' sizes, the counts
of passes and rounds, the addresses of the round keys), which it keeps in
public slots of the scratch buffer.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64

def ecbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false,
    lens := [0, 1024], bases := [(.rcx, 1, 0)] }

theorem encrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree ecbTaint s t) :
    ConstantTime isa pre pub Impl.TripleDes.X86_64.Bitslice.encrypt :=
  VG.Taint.constantTime (A := taint) ecbTaint hagree (by taint_decide)

theorem decrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree ecbTaint s t) :
    ConstantTime isa pre pub Impl.TripleDes.X86_64.Bitslice.decrypt :=
  VG.Taint.constantTime (A := taint) ecbTaint hagree (by taint_decide)

end VG.Proof.TripleDes.X86_64.Bitsliced

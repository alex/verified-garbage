import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # H′: constant time of argument handling and output loops -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

def publicRegs : List Reg := [.rbx, .r12, .r13, .r14, .r15, .rsp]

def AgreeRegs (rs : List Reg) (s t : State) : Prop := ∀ r ∈ rs, s.gpr r = t.gpr r

theorem publicRegs_callee : ∀ r ∈ publicRegs, r ∈ calleeSaved := by decide

theorem setup_rel :
    RelCT isa (AgreeRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) (.block setup)
      (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem chooseLength_rel : RelCT isa (AgreeRegs publicRegs) chooseLength
    (AgreeRegs (.rsi :: publicRegs)) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) (.rsi :: publicRegs) (by taint_decide)

theorem copy_rel : RelCT isa (AgreeRegs (.rax :: publicRegs)) copy (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs (.rax :: publicRegs))
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem emitPrefix_rel : RelCT isa (AgreeRegs publicRegs) emitPrefix (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem copyRemaining_rel : RelCT isa (AgreeRegs publicRegs) copyRemaining (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) publicRegs (by taint_decide)

theorem restore_rel : RelCT isa (AgreeRegs [.rbx]) (.block restore) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbx]) (fun _ _ hp => Taint.agree_ofRegs hp)
    (by taint_decide)

end VG.Proof.Argon2.X86_64.HPrime

import VerifiedGarbage.Proof.Rc2.Arm.Cbc.StartCT

/-! # Constant-time CBC callers -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

theorem cbc_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (Impl.Rc2.Arm.Cbc.cbc d) := by
  apply RelCT.constantTime
  apply RelCT.assoc
  apply (start_ct d).seq
  apply (maybeLoop_ct d).seq
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r2])
    (fun _ _ h => Taint.agree_ofRegs (fun r hr => h r (by have e := List.mem_singleton.mp hr; rw [e]; decide)))
  taint_decide

end VG.Proof.Rc2.Arm.Cbc

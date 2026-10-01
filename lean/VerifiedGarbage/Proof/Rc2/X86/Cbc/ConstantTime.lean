import VerifiedGarbage.Proof.Rc2.X86.Cbc.StartCT

/-! # Constant-time CBC callers -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

theorem cbc_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (Impl.Rc2.X86.Cbc.cbc d) := by
  apply RelCT.constantTime
  apply RelCT.assoc
  apply (start_ct d).seq
  apply (maybeLoop_ct d).seq
  apply RelCT.taint (A := taint) (τr [.ebp])
    (fun _ _ h => agree_regs (fun r hr => h r (by have e := List.mem_singleton.mp hr; rw [e]; decide)))
  taint_decide

end VG.Proof.Rc2.X86.Cbc

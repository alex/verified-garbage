import VerifiedGarbage.Proof.Rc4.AArch64.Lit
import VerifiedGarbage.Impl.Rc4.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64

/-- A register-table lookup needs only its base address to be public. -/
theorem lookup_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0])) lookup := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- Both the replacement index and value may be secret. -/
theorem replace_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0])) replace := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- Key scheduling has no secret-dependent control flow or memory address. -/
theorem init_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3])) init := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- A PRGA iteration needs the public stream index, pointers and length.
The table, `j`, keystream index and input byte stay secret. -/
theorem apply_step_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x9, .x12])) applyStep := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x9, .x12])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Rc4.AArch64

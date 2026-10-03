import VerifiedGarbage.Proof.Rc4.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64

/-- Key scheduling has no secret-dependent control flow or memory address:
the key bytes, `j` and the table indices stay in vector registers. -/
theorem init_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3])) init := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Rc4.AArch64

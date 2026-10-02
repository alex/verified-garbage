import VerifiedGarbage.Proof.Argon2.X86_64.FillWriteLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Both write paths have a public, fixed sequence of memory accesses. -/

namespace VG.Proof.Argon2.X86_64.FillWrite

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillWrite

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r9, .rdi, .rsi], s.gpr r = t.gpr r) code
    (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r9, .rdi, .rsi])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

end VG.Proof.Argon2.X86_64.FillWrite

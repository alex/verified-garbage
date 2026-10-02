import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! The pointer setup only branches on the public current column.
Reference coordinates may differ without changing its execution trace. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r8, .rbx, .r12, .r13, .r14, .r15], s.gpr r = t.gpr r) code
    (fun s t => ∀ r ∈ [Reg.r10], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.r8, .rbx, .r12, .r13, .r14, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) [Reg.r10] (by taint_decide)

end VG.Proof.Argon2.X86_64.FillPointers

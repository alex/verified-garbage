import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.FillColumn

/-! Merged from `Proof.Argon2.X86_64.FillColumnLit`. -/
section
/-! A checked literal for current and cyclic predecessor column calculation. -/

namespace VG

materialize_code Impl.Argon2.X86_64.FillColumn.code

end VG
end

/-! Public loop coordinates determine both columns and their branch trace. -/

namespace VG.Proof.Argon2.X86_64.FillColumn

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillColumn

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r14, .r13, .r15, .r12], s.gpr r = t.gpr r) code
    (fun s t => ∀ r ∈ [Reg.rcx, .rdi], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.r14, .r13, .r15, .r12])
    (fun _ _ h => Taint.agree_ofRegs h) [Reg.rcx, .rdi] (by taint_decide)

end VG.Proof.Argon2.X86_64.FillColumn

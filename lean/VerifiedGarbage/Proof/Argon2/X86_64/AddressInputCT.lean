import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Clearing and header preparation visit fixed offsets of public pointers. -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64

theorem ClearBlock.code_rel : RelCT isa (fun s t => s.gpr .rdi = t.gpr .rdi)
    Impl.Argon2.X86_64.ClearBlock.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem AddressHeader.code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rdi, .rbp], s.gpr r = t.gpr r)
    Impl.Argon2.X86_64.AddressHeader.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbp])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

end VG.Proof.Argon2.X86_64

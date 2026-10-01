import VerifiedGarbage.Proof.Argon2.X86_64.AddressModeLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Mode selection has a fixed trace at the public frame base. -/

namespace VG.Proof.Argon2.X86_64.AddressMode

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressMode

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.AddressMode

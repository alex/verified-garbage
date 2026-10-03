import VerifiedGarbage.Proof.Argon2.X86_64.DeriveNormalize
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! ABI argument preparation accesses only fixed offsets of the public stack. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem prepare_rel : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    Impl.Argon2.X86_64.Derive.prepare (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rsp]) (fun _ _ h =>
    Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h))
    (by taint_decide)

end VG.Proof.Argon2.X86_64.Derive

import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Final block XOR has fixed accesses determined only by its public pointers. -/

namespace VG.Proof.Argon2.X86_64.ReduceBlock

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReduceBlock

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rdi, .rsi], s.gpr r = t.gpr r) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

end VG.Proof.Argon2.X86_64.ReduceBlock

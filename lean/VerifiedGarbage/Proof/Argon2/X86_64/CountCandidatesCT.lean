import VerifiedGarbage.Proof.Argon2.X86_64.CountCandidatesLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Only the public pass affects reference-window arithmetic's trace. -/

namespace VG.Proof.Argon2.X86_64.CountCandidates

open VG VG.X86_64 VG.Impl.Argon2.X86_64.CountCandidates

theorem code_rel : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9) code
    (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r9])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.CountCandidates

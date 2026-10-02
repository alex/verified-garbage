import VerifiedGarbage.Proof.Argon2.X86_64.FirstLaneLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! The first-slice override branches only on the public position. -/

namespace VG.Proof.Argon2.X86_64.FirstLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FirstLane

theorem code_rel : RelCT isa
    (fun s t => s.gpr .r9 = t.gpr .r9 ∧ s.gpr .r14 = t.gpr .r14) code
    (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r9, .r14])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2)) (by taint_decide)

end VG.Proof.Argon2.X86_64.FirstLane

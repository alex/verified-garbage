import VerifiedGarbage.Proof.Argon2.X86_64.DivideLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # Constant-time index division, including secret numerators -/

namespace VG.Proof.Argon2.X86_64.Divide

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Divide

/-- Neither operand changes the execution trace. Public inputs additionally
produce public outputs for the parameter-setup divisions. -/
theorem code_rel :
    RelCT isa (fun s t => s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi)
      code (fun s t => ∀ r ∈ [Reg.r8, .r9], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.rdi, .rsi])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2)) [.r8, .r9] (by taint_decide)

theorem code_secret_rel : RelCT isa (fun _ _ => True) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.Divide

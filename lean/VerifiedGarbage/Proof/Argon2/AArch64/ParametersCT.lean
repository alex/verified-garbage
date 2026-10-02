import VerifiedGarbage.Proof.Argon2.AArch64.ParametersLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Rounded-memory computation reads public frame addresses with a fixed trace. -/
namespace VG.Proof.Argon2.AArch64.Parameters
open VG VG.AArch64

theorem code_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.Parameters.code (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
end VG.Proof.Argon2.AArch64.Parameters

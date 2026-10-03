import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Argon2.AArch64.Divide

/-! Merged from `Proof.Argon2.AArch64.DivideLit`. -/
section
/-! Checked literal for unrolled ARM64 reference-index division. -/
namespace VG
materialize_code Impl.Argon2.AArch64.Divide.code
end VG
end

/-! # Timing of reference-index division on ARM64 -/
namespace VG.Proof.Argon2.AArch64.Divide
open VG VG.AArch64 VG.Impl.Argon2.AArch64.Divide

theorem code_rel :
    RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1)
      code (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x4, .x5], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x1])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.2.1
      · exact h.2.2⟩) [.x4, .x5] (by taint_decide)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64.Divide

import VerifiedGarbage.Proof.Argon2.AArch64.CountCandidatesLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Only the public pass controls reference-window arithmetic. -/
namespace VG.Proof.Argon2.AArch64.CountCandidates
open VG VG.AArch64 VG.Impl.Argon2.AArch64.CountCandidates

theorem code_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x5 = t.gpr .x5) code
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x5])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h.2⟩) [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64.CountCandidates

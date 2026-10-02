import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceStartLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Branches depend only on the public position. -/
namespace VG.Proof.Argon2.AArch64.ReferenceStart
open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceStart

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [.x5, .x22, .x21], s.gpr r = t.gpr r) code
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [.x6], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x5, .x22, .x21])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [.x6] (by taint_decide)
end VG.Proof.Argon2.AArch64.ReferenceStart

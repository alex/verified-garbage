import VerifiedGarbage.Proof.Argon2.AArch64.FillPointersLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Pointer setup only branches on the public current column. -/
namespace VG.Proof.Argon2.AArch64.FillPointers
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x4, .x24, .x20, .x21, .x22, .x23], s.gpr r = t.gpr r)
    code (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x6], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x4, .x24, .x20, .x21, .x22, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [Reg.x6] (by taint_decide)
end VG.Proof.Argon2.AArch64.FillPointers

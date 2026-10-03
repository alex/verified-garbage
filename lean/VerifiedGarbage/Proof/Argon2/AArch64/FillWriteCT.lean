import VerifiedGarbage.Proof.Argon2.AArch64.FillWriteLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Both write paths have a public, fixed sequence of memory accesses. -/
namespace VG.Proof.Argon2.AArch64.FillWrite
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillWrite

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x5, .x0, .x1], s.gpr r = t.gpr r) code
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x5, .x0, .x1])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      exact h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64.FillWrite

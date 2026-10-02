import VerifiedGarbage.Proof.Argon2.AArch64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.AArch64.AddressHeaderLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Clearing and header preparation visit fixed offsets of public pointers. -/
namespace VG.Proof.Argon2.AArch64
open VG VG.AArch64

theorem ClearBlock.code_rel : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0)
    Impl.Argon2.AArch64.ClearBlock.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0])
    (fun _ _ h => ⟨h.1, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.2⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem AddressHeader.code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x0, .x19], s.gpr r = t.gpr r)
    Impl.Argon2.AArch64.AddressHeader.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x19])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)
end VG.Proof.Argon2.AArch64

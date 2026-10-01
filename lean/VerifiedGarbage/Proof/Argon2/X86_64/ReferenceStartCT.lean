import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStartLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! The public pass, slice and segment length determine the window start. -/

namespace VG.Proof.Argon2.X86_64.ReferenceStart

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceStart

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.r9, .r14, .r13], s.gpr r = t.gpr r) code
    (fun s t => s.gpr .r10 = t.gpr .r10) := by
  have h : RelCT isa
      (fun s t => ∀ r ∈ [Reg.r9, .r14, .r13], s.gpr r = t.gpr r) code
      (fun s t => ∀ r ∈ [Reg.r10], s.gpr r = t.gpr r) :=
    RelCT.taintRegs (τ := Taint.ofRegs [.r9, .r14, .r13])
    (fun _ _ h => Taint.agree_ofRegs h) [Reg.r10] (by taint_decide)
  exact h.mono (fun _ _ h => h) (fun _ _ h => h .r10 (by simp))

end VG.Proof.Argon2.X86_64.ReferenceStart

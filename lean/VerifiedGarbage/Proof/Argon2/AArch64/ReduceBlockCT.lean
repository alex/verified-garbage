import VerifiedGarbage.Proof.Argon2.AArch64.ReduceBlockLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Final block XOR has fixed accesses determined only by its public pointers. -/

namespace VG.Proof.Argon2.AArch64.ReduceBlock

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReduceBlock

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x0, .x1], s.gpr r = t.gpr r)
    code (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x1])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Argon2.AArch64.ReduceBlock

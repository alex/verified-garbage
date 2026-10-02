import VerifiedGarbage.Proof.Argon2.AArch64.DeriveLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Preparation addresses only fixed offsets of the public stack pointer. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem prepare_rel : RelCT isa (fun s t => s.sp = t.sp)
    Impl.Argon2.AArch64.Derive.prepare (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun r hr => False.elim (by
      have := RegSet.mem_ofList.mp hr
      exact List.not_mem_nil this)⟩) (by taint_decide)
end VG.Proof.Argon2.AArch64.Derive

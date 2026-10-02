import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelArgs

/-! Register-only helpers retain the filling allocation and position invariants. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64

theorem Ready.of_keeps {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s t : State}
    (h : Ready p pass lane slice index s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Ready p pass lane slice index t := by
  refine ⟨h.layout.of_keeps k, h.bounds, h.position.of_keeps k, ?_, ?_⟩
  · rw [k.mem, k.regs .x19 (by decide)]; exact h.passWord
  · rw [k.mem, k.regs .x19 (by decide)]; exact h.lanesWord

end VG.Proof.Argon2.AArch64.FillKernel

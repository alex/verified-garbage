import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelStable

/-! Transport the allocation using just its public pointers and permissions. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem Layout.of_preserved {p : Params} {s t : State} (h : Layout p s)
    (bp : t.gpr .x19 = s.gpr .x19) (sp : t.sp = s.sp)
    (base : matrix t = matrix s) (scratch : work t = work s)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Layout p t := by
  constructor
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [wr, bp]; exact h.frameWrite
  · rw [base, wr]; exact h.matrixWrite
  · rw [scratch, wr]; exact h.workWrite
  · rw [base, scratch]; exact h.matrixWork
  · rw [base, bp]; exact h.matrixFrame
  · rw [base, sp]; exact h.matrixStack
  · rw [bp, scratch]; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, scratch]; exact h.stackWork

end VG.Proof.Argon2.AArch64.FillKernel

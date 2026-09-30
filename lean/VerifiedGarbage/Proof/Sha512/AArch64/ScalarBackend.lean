import VerifiedGarbage.Proof.Sha512.AArch64.Variant

namespace VG.Proof.Sha512.AArch64.Scalar

open VG.AArch64

/-- The scalar compression backend and the checked facts its streaming callers need. -/
def backend : Compress where
  name := "vg_sha512_compress"
  code := Impl.Sha512.AArch64.compress
  verified := Proof.Sha512.AArch64.compress_verified
  noFrames := by lit_decide
  noCalls := by lit_decide
  suffix := ""
  features := []
  updateCT := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => Stream.Update.agree₀ hp) (by taint_decide)
  finalizeCT := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => Stream.Finalize.agree₀ hp) (by taint_decide)
  updateKeeps := by
    change ((instrs Impl.Sha512.AArch64.Stream.update).all _) = true
    exact instrs_keeps (by lit_decide)
  finalizeKeeps := by
    change ((instrs Impl.Sha512.AArch64.Stream.finalize).all _) = true
    exact instrs_keeps (by lit_decide)
  updateDepth := by lit_decide
  finalizeDepth := by lit_decide

end VG.Proof.Sha512.AArch64.Scalar

import VerifiedGarbage.Proof.Sha1.AArch64.Variant
import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Compress

namespace VG.Proof.Sha1.AArch64.Sha2

open VG.AArch64

/-- The sha2 compression backend and the checked facts its streaming callers need. -/
def backend : Compress where
  name := "vg_sha1_compress_sha2"
  code := Impl.Sha1.AArch64.Sha2.compress
  verified := Proof.Sha1.AArch64.Sha2.compress_verified
  noFrames := by lit_decide
  keepsV := by lit_decide
  suffix := "_sha2"
  features := ["sha2"]
  updateCT := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide)
  finalizeCT := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide)
  updateKeeps := by lit_decide
  finalizeKeeps := by lit_decide
  updateDepth := by lit_decide
  finalizeDepth := by lit_decide

end VG.Proof.Sha1.AArch64.Sha2

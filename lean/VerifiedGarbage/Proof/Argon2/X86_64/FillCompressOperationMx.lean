import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressOperation
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressLit

/-! Baseline compression and the block write preserve all of MXCSR. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

theorem operation_mx_ok (s : State) (h : OperationReady s) :
    WP isa operation s fun t => OperationDone s t ∧ t.mxcsr = s.mxcsr :=
  WP.mono_mx (by lit_decide) (operation_ok s h) (fun _ done mx => ⟨done, mx⟩)

end VG.Proof.Argon2.X86_64.FillCompress

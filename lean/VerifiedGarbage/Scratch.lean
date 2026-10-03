import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
open VG VG.X86_64
set_option profiler true in
example : ∃ hc, ((taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r11, .rsp])
    (Impl.AesGcm.X86_64.Blocks.stitchPart Impl.Gcm.X86_64.Stitch.enc) hc).map fun τ' =>
      (RegSet.ofList [.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩
set_option profiler true in
example : ∃ hc, ((taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r11, .rsp])
    (Impl.AesGcm.X86_64.Blocks.stitchPart Impl.Gcm.X86_64.Stitch.dec) hc).map fun τ' =>
      (RegSet.ofList [.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

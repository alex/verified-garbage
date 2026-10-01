import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
import VerifiedGarbage.Proof.ChaCha20.AArch64.XorContract
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64

namespace VG.Proof.ChaCha20.AArch64

open VG VG.AArch64

/-- Facts needed by the generic stream and AEAD callers. The functional proofs
are shared; each concrete backend supplies its mechanical taint checks. -/
structure BlockImpl where
  callee : Impl.ChaCha20.AArch64.Callee
  features : List String
  ok : ∀ s, blockAArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ blockAArch64.post s s'
  noFrames : callee.code.noFrames = true
  keeps : ∀ r ∈ [Reg.x0, .x1], ∀ i ∈ instrs callee.code, dstOf i ≠ some r
  xorKeeps : ∀ r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28],
    ∀ i ∈ instrs (Impl.ChaCha20.AArch64.Xor.xorWith callee), dstOf i ≠ some r
  xorNoFrames : (Impl.ChaCha20.AArch64.Xor.xorWith callee).noFrames = true
  xorTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.ChaCha20.AArch64.Xor.xorWith callee) h).isSome = true
  sealTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.ChaCha20Poly1305.AArch64.sealWith callee) h).isSome = true
  openTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.ChaCha20Poly1305.AArch64.openWith callee) h).isSome = true

end VG.Proof.ChaCha20.AArch64

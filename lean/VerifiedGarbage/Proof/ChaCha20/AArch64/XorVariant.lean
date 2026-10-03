import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched

namespace VG.Proof.ChaCha20.AArch64

open VG VG.AArch64

/-- A verified stream backend, shared by the public stream and every AEAD caller. -/
structure XorImpl where
  callee : Impl.ChaCha20.AArch64.XorCallee
  features : List String
  /-- Notes on the implementation, for the documentation of `vg_chacha20_xor` and its
  variants. -/
  notes : List String
  ok : ∀ s, xorAArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ xorAArch64.post s s'
  ct : ConstantTime isa xorAArch64.pre xorAArch64.pub callee.code
  noFrames : callee.code.noFrames = true
  /-- Whether ChaCha20-Poly1305 absorbs the data inside the eight-block kernel
  (`Impl/ChaCha20Poly1305/AArch64/Stitched.lean`), calling the backend for the
  rest, rather than calling it for all of the data. -/
  stitched : Bool
  sealTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.ChaCha20Poly1305.AArch64.sealCode callee stitched) h).isSome = true
  openTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.ChaCha20Poly1305.AArch64.openCode callee stitched) h).isSome = true

theorem XorImpl.verified (v : XorImpl) :
    Verified AArch64.target v.callee.code (Spec.ChaCha20.xorContract AArch64.abi) :=
  Verified.of_correct v.ok v.ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, AArch64.abi, AArch64.argRegs,
      xorAArch64] [Xor.sat] using Xor.sat)

end VG.Proof.ChaCha20.AArch64

import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Lit

namespace VG.Proof.ChaCha20.AArch64.XorImpl

open VG VG.AArch64

/-- Scalar stream, also used for the short tail of the four-block backend. -/
def scalar : XorImpl where
  callee := .scalar
  features := []
  ok := Xor.xor_correct BlockImpl.scalar
  ct := Xor.xor_ct BlockImpl.scalar
  noFrames := BlockImpl.scalar.xorNoFrames
  sealTaint := ⟨_, by taint_decide⟩
  openTaint := ⟨_, by taint_decide⟩

/-- Four independent ChaCha20 blocks in baseline AdvSIMD lanes. -/
def neon : XorImpl where
  callee := .neon
  features := []
  ok := Neon4.xor_correct
  ct := Neon4.xor_ct
  noFrames := Neon4.xor_noFrames
  sealTaint := ⟨_, by taint_decide⟩
  openTaint := ⟨_, by taint_decide⟩

end VG.Proof.ChaCha20.AArch64.XorImpl

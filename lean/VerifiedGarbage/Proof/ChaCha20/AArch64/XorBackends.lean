import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Lit

namespace VG.Proof.ChaCha20.AArch64.XorImpl

open VG VG.AArch64

/-- Scalar stream, also used for the short tail of the eight-block backend. -/
def scalar : XorImpl where
  callee := .scalar
  features := []
  notes := ["Calls `vg_chacha20_block` for each 64 bytes."]
  ok := Xor.xor_correct BlockImpl.scalar
  ct := Xor.xor_ct BlockImpl.scalar
  noFrames := BlockImpl.scalar.xorNoFrames
  stitched := false
  sealTaint := ⟨_, by taint_decide⟩
  openTaint := ⟨_, by taint_decide⟩

/-- Eight ChaCha20 blocks interleaved across AdvSIMD and integer registers. -/
def neon : XorImpl where
  callee := .neon
  features := []
  notes := ["Interleaves six NEON blocks with two integer blocks, processing 512 bytes at a time."]
  ok := Mixed8.xor_correct
  ct := Mixed8.xor_ct
  noFrames := Mixed8.xor_noFrames
  stitched := true
  sealTaint := ⟨_, by taint_decide⟩
  openTaint := ⟨_, by taint_decide⟩

/-- The eight-block kernel with SVE2: each AdvSIMD XOR and rotation of the
vector blocks is one XAR. -/
def sve2 : XorImpl where
  callee := .sve2
  features := ["sve2"]
  notes := ["Interleaves six NEON blocks with two integer blocks, processing 512 bytes at a time; " ++
    "each XOR and rotation of the NEON blocks is one SVE2 XAR."]
  ok := Mixed8.xor_correct
  ct := Mixed8.xor_ct
  noFrames := Mixed8.xor_noFrames
  stitched := true
  sealTaint := ⟨_, by taint_decide⟩
  openTaint := ⟨_, by taint_decide⟩

end VG.Proof.ChaCha20.AArch64.XorImpl

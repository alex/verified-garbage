import VerifiedGarbage.Impl.Argon2.AArch64.HPrime
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # H′: requirements of its BLAKE2b streaming backend -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure HashOk (h : Hash) : Prop where
  init : Verified AArch64.target h.init (Spec.Blake2.initBContract AArch64.abi)
  update : Verified AArch64.target h.update (Spec.Blake2.updateBContract AArch64.abi 16)
  finalize : Verified AArch64.target h.finalize (Spec.Blake2.finalizeBContract AArch64.abi 16)
  initNoFrames : h.init.noFrames = true
  initDepth : h.init.aarch64Depth = 0
  updateDepth : h.update.aarch64Depth = 1
  finalizeDepth : h.finalize.aarch64Depth = 1

end VG.Proof.Argon2.AArch64.HPrime

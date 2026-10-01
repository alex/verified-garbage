import VerifiedGarbage.Impl.Argon2.X86_64.HPrime
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# H′: the BLAKE2b streaming callee

The H′ proof uses the shared BLAKE2b streaming contracts. Its hash
implementation is supplied by a variant, including the stack bounds and
instruction properties needed to compose verified calls. No compression
implementation is chosen here.
-/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

/-- Obligations of any streaming BLAKE2b backend used by H′. -/
structure HashOk (h : Hash) : Prop where
  init : Verified X86_64.target h.init (Spec.Blake2.initBContract X86_64.abi)
  update : Verified X86_64.target h.update (Spec.Blake2.updateBContract X86_64.abi 8)
  finalize : Verified X86_64.target h.finalize (Spec.Blake2.finalizeBContract X86_64.abi 8)
  initNoSp : NoSp h.init
  updateNoSp : NoSp h.update
  finalizeNoSp : NoSp h.finalize
  initDepth : h.init.depth = 0
  updateDepth : h.update.depth = 1
  finalizeDepth : h.finalize.depth = 1

end VG.Proof.Argon2.X86_64.HPrime

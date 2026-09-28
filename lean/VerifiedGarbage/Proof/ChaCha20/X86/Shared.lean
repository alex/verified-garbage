import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20.X86.Block
import VerifiedGarbage.Spec.ChaCha20.Contract

/-!
# ChaCha20 on X86: the shared contract

Untrusted: everything here is checked by Lean. The proof is written against
a per-target contract (`Proof/ChaCha20/X86/Contract.lean`); this theorem
moves it to the shared contract of `Spec/ChaCha20/Contract.lean`, which the
artifact is emitted with.
-/

namespace VG.Proof.ChaCha20.X86.Shared

theorem block :
    Verified X86.target Impl.ChaCha20.X86.block (Spec.ChaCha20.blockContract X86.abi) :=
  Proof.ChaCha20.X86.block_verified.of_implies (by
    contract_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig,
      Proof.ChaCha20.blockX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.ChaCha20.X86.satState, Proof.ChaCha20.X86.satMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using Proof.ChaCha20.X86.satState)

end VG.Proof.ChaCha20.X86.Shared

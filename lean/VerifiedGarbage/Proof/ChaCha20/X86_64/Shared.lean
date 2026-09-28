import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20.X86_64.Block
import VerifiedGarbage.Spec.ChaCha20.Contract

/-!
# ChaCha20 on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/ChaCha20/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/ChaCha20/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.ChaCha20.X86_64.Shared

theorem block :
    Verified X86_64.target Impl.ChaCha20.X86_64.block (Spec.ChaCha20.blockContract X86_64.abi) :=
  Proof.ChaCha20.X86_64.block_verified.of_implies (by
    contract_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig,
      Proof.ChaCha20.blockX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.ChaCha20.X86_64.satState] using Proof.ChaCha20.X86_64.satState)

end VG.Proof.ChaCha20.X86_64.Shared

import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Block
import VerifiedGarbage.Spec.ChaCha20.Contract

/-!
# ChaCha20 on PPC64LE: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/ChaCha20/PPC64LE/Contract.lean`); these theorems move
them to the shared contracts of `Spec/ChaCha20/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.ChaCha20.PPC64LE.Shared

theorem block :
    Verified PPC64LE.target Impl.ChaCha20.PPC64LE.block (Spec.ChaCha20.blockContract PPC64LE.abi) :=
  Proof.ChaCha20.PPC64LE.block_verified.of_implies (by
    contract_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig,
      Proof.ChaCha20.blockPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.ChaCha20.PPC64LE.satState] using Proof.ChaCha20.PPC64LE.satState)

end VG.Proof.ChaCha20.PPC64LE.Shared

import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20.X86.Block
import VerifiedGarbage.Proof.ChaCha20.X86.Xor
import VerifiedGarbage.Spec.ChaCha20.Contract

/-!
# ChaCha20 on X86: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/ChaCha20/X86/Contract.lean`); these theorems
move them to the shared contracts of `Spec/ChaCha20/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.ChaCha20.X86.Shared

theorem block :
    Verified X86.target Impl.ChaCha20.X86.block (Spec.ChaCha20.blockContract X86.abi) :=
  Proof.ChaCha20.X86.block_verified.of_implies (by
    contract_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig,
      Proof.ChaCha20.blockX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.ChaCha20.X86.satState, Proof.ChaCha20.X86.satMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using Proof.ChaCha20.X86.satState)

/-- `vg_chacha20_xor`: its calls of `vg_chacha20_block` use the 12 bytes of
stack below `esp` (the frame of its two arguments, and its return address). -/
theorem xor :
    Verified X86.target Impl.ChaCha20.X86.Xor.xor (Spec.ChaCha20.xorContract X86.abi 12) :=
  Proof.ChaCha20.X86.Xor.xor_verified.of_implies (by
    contract_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig,
      Proof.ChaCha20.xorX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.ChaCha20.X86.Xor.sat, Proof.ChaCha20.X86.Xor.satMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using Proof.ChaCha20.X86.Xor.sat)

end VG.Proof.ChaCha20.X86.Shared

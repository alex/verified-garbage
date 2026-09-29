import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.ChaCha20.Arm.Block
import VerifiedGarbage.Proof.ChaCha20.Arm.Xor
import VerifiedGarbage.Spec.ChaCha20.Contract

/-!
# ChaCha20 on Arm: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/ChaCha20/Arm/Contract.lean`); these theorems move
them to the shared contracts of `Spec/ChaCha20/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.ChaCha20.Arm.Shared

theorem block : Verified Arm.target Impl.ChaCha20.Arm.block (Spec.ChaCha20.blockContract Arm.abi) :=
  Proof.ChaCha20.Arm.block_verified.of_implies (by
    contract_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig, Proof.ChaCha20.blockArm,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.ChaCha20.Arm.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.ChaCha20.Arm.satState)

theorem xor : Verified Arm.target Impl.ChaCha20.Arm.Xor.xor (Spec.ChaCha20.xorContract Arm.abi) :=
  Proof.ChaCha20.Arm.Xor.xor_verified.of_implies (by
    contract_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, Proof.ChaCha20.xorArm,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.ChaCha20.Arm.Xor.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.ChaCha20.Arm.Xor.sat)

end VG.Proof.ChaCha20.Arm.Shared

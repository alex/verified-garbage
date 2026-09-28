import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Hmac.Arm.Finalize
import VerifiedGarbage.Proof.Hmac.Arm.Init
import VerifiedGarbage.Spec.Hmac.Contract

/-!
# Hmac on Arm: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Hmac/Arm/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Hmac/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Hmac.Arm.Shared

theorem init :
    Verified Arm.target Impl.Hmac.Arm.init (Spec.Hmac.initSha256Contract Arm.abi) :=
  Proof.Hmac.Arm.Init.init_verified.of_implies (by
    contract_implies [Spec.Hmac.initSha256Contract, Spec.Hmac.initSha256Sig,
      Proof.Hmac.initSha256Arm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Hmac.Arm.Init.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Hmac.Arm.Init.sat)

theorem finalize :
    Verified Arm.target Impl.Hmac.Arm.finalize (Spec.Hmac.finalizeSha256OutContract Arm.abi) :=
  Proof.Hmac.Arm.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Hmac.finalizeSha256OutContract, Spec.Hmac.finalizeSha256OutSig,
      Proof.Hmac.finalizeSha256Arm, Proof.Sha256.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Hmac.Arm.Finalize.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Hmac.Arm.Finalize.sat)

end VG.Proof.Hmac.Arm.Shared

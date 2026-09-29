import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Sha1.Arm.Compress
import VerifiedGarbage.Proof.Sha1.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Sha1.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha1.Arm.Stream.Update
import VerifiedGarbage.Spec.Sha1.Contract

/-!
# Sha1 on Arm: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha1/Arm/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha1/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Sha1.Arm.Shared

theorem compress :
    Verified Arm.target Impl.Sha1.Arm.compress (Spec.Sha1.compressContract Arm.abi) :=
  Proof.Sha1.Arm.compress_verified.of_implies (by
    contract_implies [Spec.Sha1.compressContract, Spec.Sha1.compressSig,
      Proof.Sha1.compressArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha1.Arm.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha1.Arm.satState)

theorem init : Verified Arm.target Impl.Sha1.Arm.Stream.init (Spec.Sha1.initContract Arm.abi) :=
  Proof.Sha1.Arm.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha1.initContract, Spec.Sha1.initSig, Proof.Sha1.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha1.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha1.Arm.Stream.initSat)

theorem update :
    Verified Arm.target Impl.Sha1.Arm.Stream.update (Spec.Sha1.updateContract Arm.abi) :=
  Proof.Sha1.Arm.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha1.updateContract, Spec.Sha1.updateSig, Proof.Sha1.updateArm,
      Proof.Sha1.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha1.Arm.Stream.Update.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha1.Arm.Stream.Update.sat)

theorem finalize :
    Verified Arm.target Impl.Sha1.Arm.Stream.finalize (Spec.Sha1.finalizeContract Arm.abi) :=
  Proof.Sha1.Arm.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Sha1.finalizeContract, Spec.Sha1.finalizeSig,
      Proof.Sha1.finalizeArm, Proof.Sha1.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Sha1.Arm.Stream.Finalize.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha1.Arm.Stream.Finalize.sat)

end VG.Proof.Sha1.Arm.Shared

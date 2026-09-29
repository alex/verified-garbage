import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
import VerifiedGarbage.Spec.Sha256.Contract

/-!
# Sha256 on Arm: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha256/Arm/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha256/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Sha256.Arm.Shared

theorem compress :
    Verified Arm.target Impl.Sha256.Arm.compress (Spec.Sha256.compressContract Arm.abi) :=
  Proof.Sha256.Arm.compress_verified.of_implies (by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig,
      Proof.Sha256.compressArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha256.Arm.satState)

theorem init : Verified Arm.target Impl.Sha256.Arm.Stream.init (Spec.Sha256.initContract Arm.abi) :=
  Proof.Sha256.Arm.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha256.Arm.Stream.initSat)

theorem update :
    Verified Arm.target Impl.Sha256.Arm.Stream.update (Spec.Sha256.updateContract Arm.abi) :=
  Proof.Sha256.Arm.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Proof.Sha256.updateArm,
      Proof.Sha256.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Stream.Update.sat, MdStream.Arm.Update.sat, Impl.Sha256.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha256.Arm.Stream.Update.sat)

theorem finalize :
    Verified Arm.target Impl.Sha256.Arm.Stream.finalize (Spec.Sha256.finalizeContract Arm.abi) :=
  Proof.Sha256.Arm.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig,
      Proof.Sha256.finalizeArm, Proof.Sha256.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Stream.Finalize.sat, MdStream.Arm.Finalize.sat, MdStream.Arm.Finalize.satBase,
        Impl.Sha256.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha256.Arm.Stream.Finalize.sat)

end VG.Proof.Sha256.Arm.Shared

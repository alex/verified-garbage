import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Md5.Arm.Compress
import VerifiedGarbage.Proof.Md5.Arm.Stream.Init
import VerifiedGarbage.Proof.Md5.Arm.Stream.Md
import VerifiedGarbage.Spec.Md5.Contract

/-!
# Md5 on Arm: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Md5/Arm/Compress.lean`); these theorems move
them to the shared contracts of `Spec/Md5/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Md5.Arm.Shared

theorem compress :
    Verified Arm.target Impl.Md5.Arm.compress (Spec.Md5.compressContract Arm.abi) :=
  Proof.Md5.Arm.compress_verified.of_implies (by
    sig_implies [Spec.Md5.compressContract, Spec.Md5.compressSig,
      Proof.Md5.compressArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Md5.Arm.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Md5.Arm.satState)

theorem init : Verified Arm.target Impl.Md5.Arm.Stream.init (Spec.Md5.initContract Arm.abi) :=
  Proof.Md5.Arm.Stream.init_verified.of_implies (by
    contract_implies [Spec.Md5.initContract, Spec.Md5.initSig, Proof.Md5.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Md5.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Md5.Arm.Stream.initSat)

theorem update :
    Verified Arm.target Impl.Md5.Arm.Stream.update (Spec.Md5.updateContract Arm.abi) :=
  Proof.Md5.Arm.Stream.Update.update_verified.of_implies (by
    sig_implies [Spec.Md5.updateContract, Spec.Md5.updateSig, Proof.Md5.updateArm,
      Proof.Md5.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Md5.Arm.Stream.Update.sat, MdStream.Arm.Update.sat, Impl.Md5.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Md5.Arm.Stream.Update.sat)

theorem finalize :
    Verified Arm.target Impl.Md5.Arm.Stream.finalize (Spec.Md5.finalizeContract Arm.abi) :=
  Proof.Md5.Arm.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Md5.finalizeContract, Spec.Md5.finalizeSig,
      Proof.Md5.finalizeArm, Proof.Md5.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Md5.Arm.Stream.Finalize.sat, MdStream.Arm.Finalize.sat, MdStream.Arm.Finalize.satBase,
        Impl.Md5.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Md5.Arm.Stream.Finalize.sat)

end VG.Proof.Md5.Arm.Shared

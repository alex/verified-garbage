import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Poly1305.Arm.Init
import VerifiedGarbage.Proof.Poly1305.Arm.Update
import VerifiedGarbage.Proof.Poly1305.Arm.Finalize
import VerifiedGarbage.Spec.Poly1305.Contract

/-!
# Poly1305 on 32-bit ARM: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Poly1305/Arm/Contract.lean`); these theorems
move them to the shared contracts of `Spec/Poly1305/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Poly1305.Arm.Shared

theorem init : Verified Arm.target Impl.Poly1305.Arm.init (Spec.Poly1305.initContract Arm.abi) :=
  Proof.Poly1305.Arm.init_verified.of_implies (by
    contract_implies [Spec.Poly1305.initContract, Spec.Poly1305.initSig, Proof.Poly1305.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Poly1305.Arm.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Poly1305.Arm.initSat)

theorem blocks : Verified Arm.target Impl.Poly1305.Arm.blocks (Spec.Poly1305.blocksContract Arm.abi) :=
  Proof.Poly1305.Arm.blocks_verified.of_implies (by
    contract_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig, Proof.Poly1305.blocksArm,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Poly1305.Arm.blocksSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Poly1305.Arm.blocksSat)

theorem update : Verified Arm.target Impl.Poly1305.Arm.update (Spec.Poly1305.updateContract Arm.abi) :=
  Proof.Poly1305.Arm.Update.update_verified.of_implies (by
    contract_implies [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, Proof.Poly1305.updateArm,
      Proof.Poly1305.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Poly1305.Arm.Update.updateSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Poly1305.Arm.Update.updateSat)

theorem finalize :
    Verified Arm.target Impl.Poly1305.Arm.finalize (Spec.Poly1305.finalizeContract Arm.abi) :=
  Proof.Poly1305.Arm.Fin.finalize_verified.of_implies (by
    contract_implies [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
      Proof.Poly1305.finalizeArm, Proof.Poly1305.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Poly1305.Arm.Fin.finalizeSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Poly1305.Arm.Fin.finalizeSat)

end VG.Proof.Poly1305.Arm.Shared

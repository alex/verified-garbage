import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Update
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Sha512 on Arm: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha512/Arm/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha512/Contract.lean`, which the
artifacts are emitted with. (There is no 32-bit ARM compression function:
see `VG.Impl.Sha512.Arm`.)
-/

namespace VG.Proof.Sha512.Arm.Shared

theorem init (iv : Spec.Sha512.HashValue) :
    Verified Arm.target (Impl.Sha512.Arm.Stream.init iv) (Spec.Sha512.initContract Arm.abi iv) :=
  (Proof.Sha512.Arm.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initArm, Arm.abi,
      Arm.argRegs, Arm.classify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha512.Arm.Stream.initSat)

theorem update :
    Verified Arm.target Impl.Sha512.Arm.Stream.update (Spec.Sha512.updateContract Arm.abi) :=
  Proof.Sha512.Arm.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha512.updateContract, Spec.Sha512.updateSig, Proof.Sha512.updateArm,
      Proof.Sha512.countArm, Arm.abi, Arm.argRegs, Arm.classify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Stream.Update.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha512.Arm.Stream.Update.sat)

theorem finalize :
    Verified Arm.target Impl.Sha512.Arm.Stream.finalize (Spec.Sha512.finalizeContract Arm.abi) :=
  Proof.Sha512.Arm.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig,
      Proof.Sha512.finalizeArm, Proof.Sha512.countArm, Arm.abi, Arm.argRegs, Arm.classify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Stream.Finalize.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha512.Arm.Stream.Finalize.sat)

end VG.Proof.Sha512.Arm.Shared

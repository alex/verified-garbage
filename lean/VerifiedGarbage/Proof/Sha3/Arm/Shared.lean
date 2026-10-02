import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Sha3.Arm.Permute
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
import VerifiedGarbage.Spec.Sha3.Contract

/-!
# SHA-3 on ARMv7: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha3/Arm/Permute.lean`); these theorems move them to the shared
contracts of `Spec/Sha3/Contract.lean`, which the artifacts are emitted with.
The functions use no stack: `bl` leaves the return address in `lr`, which each
streaming function saves in its scratch space.
-/

namespace VG.Proof.Sha3.Arm.Shared

/-- The returned `usize` is the low word, `r0`, of the returned pair. -/
theorem setWidth_append32 (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt b.isLt]
  omega

theorem permute :
    Verified Arm.target Impl.Sha3.Arm.permute (Spec.Sha3.permuteContract Arm.abi) :=
  Proof.Sha3.Arm.permute_verified.of_implies (by
    contract_implies [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, Proof.Sha3.permuteArm,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha3.Arm.satState] using Proof.Sha3.Arm.satState)

theorem absorb :
    Verified Arm.target Impl.Sha3.Arm.Stream.absorb (Spec.Sha3.absorbContract Arm.abi) :=
  Proof.Sha3.Arm.Stream.Absorb.absorb_verified.of_implies (by
    contract_implies [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Proof.Sha3.absorbArm,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, setWidth_append32]
      [Proof.Sha3.Arm.Stream.Absorb.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Sha3.Arm.Stream.Absorb.sat)

theorem pad :
    Verified Arm.target Impl.Sha3.Arm.Stream.pad (Spec.Sha3.padContract Arm.abi) :=
  Proof.Sha3.Arm.Stream.Pad.pad_verified.of_implies (by
    contract_implies [Spec.Sha3.padContract, Spec.Sha3.padSig, Proof.Sha3.padArm,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha3.Arm.Stream.Pad.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Sha3.Arm.Stream.Pad.sat)

theorem squeeze :
    Verified Arm.target Impl.Sha3.Arm.Stream.squeeze (Spec.Sha3.squeezeContract Arm.abi) :=
  Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.of_implies (by
    contract_implies [Spec.Sha3.squeezeContract, Spec.Sha3.squeezeSig, Proof.Sha3.squeezeArm,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, setWidth_append32]
      [Proof.Sha3.Arm.Stream.Squeeze.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Sha3.Arm.Stream.Squeeze.sat)

end VG.Proof.Sha3.Arm.Shared

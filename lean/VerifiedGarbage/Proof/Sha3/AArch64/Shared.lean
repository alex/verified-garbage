import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Spec.Sha3.Contract

/-!
# SHA-3 on AArch64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha3/AArch64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha3/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Sha3.AArch64.Shared

theorem permute :
    Verified AArch64.target Impl.Sha3.AArch64.permute (Spec.Sha3.permuteContract AArch64.abi) :=
  Proof.Sha3.AArch64.permute_verified.of_implies (by
    contract_implies [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, Proof.Sha3.permuteAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha3.AArch64.satState] using Proof.Sha3.AArch64.satState)

theorem absorb :
    Verified AArch64.target Impl.Sha3.AArch64.Stream.absorb (Spec.Sha3.absorbContract AArch64.abi 16) :=
  Proof.Sha3.AArch64.Stream.Absorb.absorb_verified.of_implies (by
    contract_implies [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Proof.Sha3.absorbAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha3.AArch64.Stream.Absorb.sat] using Proof.Sha3.AArch64.Stream.Absorb.sat)

theorem pad :
    Verified AArch64.target Impl.Sha3.AArch64.Stream.pad (Spec.Sha3.padContract AArch64.abi 16) :=
  Proof.Sha3.AArch64.Stream.Pad.pad_verified.of_implies (by
    contract_implies [Spec.Sha3.padContract, Spec.Sha3.padSig, Proof.Sha3.padAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha3.AArch64.Stream.Pad.sat] using Proof.Sha3.AArch64.Stream.Pad.sat)

theorem squeeze :
    Verified AArch64.target Impl.Sha3.AArch64.Stream.squeeze (Spec.Sha3.squeezeContract AArch64.abi 16) :=
  Proof.Sha3.AArch64.Stream.Squeeze.squeeze_verified.of_implies (by
    contract_implies [Spec.Sha3.squeezeContract, Spec.Sha3.squeezeSig, Proof.Sha3.squeezeAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha3.AArch64.Stream.Squeeze.sat] using Proof.Sha3.AArch64.Stream.Squeeze.sat)

end VG.Proof.Sha3.AArch64.Shared

import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
import VerifiedGarbage.Spec.Sha3.Contract

/-!
# SHA-3 on x86-64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha3/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha3/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Sha3.X86_64.Shared

theorem permute :
    Verified X86_64.target Impl.Sha3.X86_64.permute (Spec.Sha3.permuteContract X86_64.abi) :=
  -- `permuteX86_64` also says that `rdi` and `rsi` are returned unchanged,
  -- which the shared contract leaves out.
  Proof.Sha3.X86_64.permute_verified.of_implies
    { pre := by
        implies_pre [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, Proof.Sha3.permuteX86_64,
          X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_unfold [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, Proof.Sha3.permuteX86_64,
          X86_64.abi, X86_64.argRegs]
        exact h.1
      pub := by
        implies_pub [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, Proof.Sha3.permuteX86_64,
          X86_64.abi, X86_64.argRegs]
      sat := by
        implies_sat [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, Proof.Sha3.permuteX86_64,
          X86_64.abi, X86_64.argRegs, Proof.Sha3.X86_64.satState] using Proof.Sha3.X86_64.satState }

theorem absorb :
    Verified X86_64.target Impl.Sha3.X86_64.Stream.absorb (Spec.Sha3.absorbContract X86_64.abi 8) :=
  Proof.Sha3.X86_64.Stream.Absorb.absorb_verified.of_implies (by
    contract_implies [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Proof.Sha3.absorbX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha3.X86_64.Stream.Absorb.sat] using Proof.Sha3.X86_64.Stream.Absorb.sat)

theorem pad :
    Verified X86_64.target Impl.Sha3.X86_64.Stream.pad (Spec.Sha3.padContract X86_64.abi 8) :=
  Proof.Sha3.X86_64.Stream.Pad.pad_verified.of_implies (by
    contract_implies [Spec.Sha3.padContract, Spec.Sha3.padSig, Proof.Sha3.padX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha3.X86_64.Stream.Pad.sat] using Proof.Sha3.X86_64.Stream.Pad.sat)

theorem squeeze :
    Verified X86_64.target Impl.Sha3.X86_64.Stream.squeeze (Spec.Sha3.squeezeContract X86_64.abi 8) :=
  Proof.Sha3.X86_64.Stream.Squeeze.squeeze_verified.of_implies (by
    contract_implies [Spec.Sha3.squeezeContract, Spec.Sha3.squeezeSig, Proof.Sha3.squeezeX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha3.X86_64.Stream.Squeeze.sat] using Proof.Sha3.X86_64.Stream.Squeeze.sat)

end VG.Proof.Sha3.X86_64.Shared

import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Poly1305.AArch64.Finalize
import VerifiedGarbage.Spec.Poly1305.Contract

/-!
# Poly1305 on AArch64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Poly1305/AArch64/Contract.lean`); these theorems
move them to the shared contracts of `Spec/Poly1305/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Poly1305.AArch64.Shared

theorem init :
    Verified AArch64.target Impl.Poly1305.AArch64.init (Spec.Poly1305.initContract AArch64.abi) :=
  Proof.Poly1305.AArch64.init_verified.of_implies (by
    contract_implies [Spec.Poly1305.initContract, Spec.Poly1305.initSig,
      Proof.Poly1305.initAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Poly1305.AArch64.initSat] using Proof.Poly1305.AArch64.initSat)

theorem blocks :
    Verified AArch64.target Impl.Poly1305.AArch64.blocks (Spec.Poly1305.blocksContract AArch64.abi) :=
  Proof.Poly1305.AArch64.blocks_verified.of_implies (by
    contract_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig,
      Proof.Poly1305.blocksAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Poly1305.AArch64.blocksSat] using Proof.Poly1305.AArch64.blocksSat)

theorem finalize :
    Verified AArch64.target Impl.Poly1305.AArch64.finalize
      (Spec.Poly1305.finalizeContract AArch64.abi) :=
  Proof.Poly1305.AArch64.finalize_verified.of_implies (by
    contract_implies [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
      Proof.Poly1305.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Poly1305.AArch64.finalizeSat] using Proof.Poly1305.AArch64.finalizeSat)

end VG.Proof.Poly1305.AArch64.Shared

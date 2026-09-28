import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Finalize
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Update
import VerifiedGarbage.Spec.Sha256.Contract

/-!
# Sha256 on AArch64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha256/AArch64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha256/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Sha256.AArch64.Shared

theorem compress :
    Verified AArch64.target Impl.Sha256.AArch64.compress (Spec.Sha256.compressContract AArch64.abi) :=
  Proof.Sha256.AArch64.compress_verified.of_implies (by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig,
      Proof.Sha256.compressAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sha256.AArch64.satState] using Proof.Sha256.AArch64.satState)

theorem init :
    Verified AArch64.target Impl.Sha256.AArch64.Stream.init (Spec.Sha256.initContract AArch64.abi) :=
  Proof.Sha256.AArch64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha256.AArch64.Stream.initSat] using Proof.Sha256.AArch64.Stream.initSat)

theorem update :
    Verified AArch64.target Impl.Sha256.AArch64.Stream.update (Spec.Sha256.updateContract AArch64.abi 16) :=
  Proof.Sha256.AArch64.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Proof.Sha256.updateAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha256.AArch64.Stream.Update.sat] using Proof.Sha256.AArch64.Stream.Update.sat)

theorem finalize :
    Verified AArch64.target Impl.Sha256.AArch64.Stream.finalize (Spec.Sha256.finalizeContract AArch64.abi 16) :=
  Proof.Sha256.AArch64.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig,
      Proof.Sha256.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sha256.AArch64.Stream.Finalize.sat] using Proof.Sha256.AArch64.Stream.Finalize.sat)

end VG.Proof.Sha256.AArch64.Shared

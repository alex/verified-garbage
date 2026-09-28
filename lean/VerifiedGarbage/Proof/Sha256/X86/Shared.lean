import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha256.X86.Stream.Init
import VerifiedGarbage.Proof.Sha256.X86.Stream.Update
import VerifiedGarbage.Proof.Sha256.X86.Stream.Finalize
import VerifiedGarbage.Spec.Sha256.Contract

/-!
# Sha256 on X86: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha256/X86/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha256/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Sha256.X86.Shared

theorem compress :
    Verified X86.target Impl.Sha256.X86.compress (Spec.Sha256.compressContract X86.abi) :=
  Proof.Sha256.X86.compress_verified.of_implies (by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig, Proof.Sha256.compressX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha256.X86.satState, Proof.Sha256.X86.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Proof.Sha256.X86.satState)

theorem init :
    Verified X86.target Impl.Sha256.X86.Stream.init (Spec.Sha256.initContract X86.abi) :=
  Proof.Sha256.X86.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha256.X86.Stream.initSat, Proof.Sha256.X86.Stream.initSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Proof.Sha256.X86.Stream.initSat)

theorem update :
    Verified X86.target Impl.Sha256.X86.Stream.update (Spec.Sha256.updateContract X86.abi) :=
  Proof.Sha256.X86.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Proof.Sha256.updateX86, Proof.Sha256.countX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha256.X86.Stream.Update.sat, Proof.Sha256.X86.Stream.Update.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Proof.Sha256.X86.Stream.Update.sat)

theorem finalize :
    Verified X86.target Impl.Sha256.X86.Stream.finalize (Spec.Sha256.finalizeContract X86.abi) :=
  Proof.Sha256.X86.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Proof.Sha256.finalizeX86, Proof.Sha256.countX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha256.X86.Stream.Finalize.sat, Proof.Sha256.X86.Stream.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Proof.Sha256.X86.Stream.Finalize.sat)

end VG.Proof.Sha256.X86.Shared

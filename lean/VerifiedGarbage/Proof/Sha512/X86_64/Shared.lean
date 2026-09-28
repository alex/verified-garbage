import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Update
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Sha512 on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha512/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha512/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Sha512.X86_64.Shared

theorem compress :
    Verified X86_64.target Impl.Sha512.X86_64.compress (Spec.Sha512.compressContract X86_64.abi) :=
  Proof.Sha512.X86_64.compress_verified.of_implies (by
    contract_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig,
      Proof.Sha512.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha512.X86_64.satState] using Proof.Sha512.X86_64.satState)

theorem init (iv : Spec.Sha512.HashValue) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.init iv) (Spec.Sha512.initContract X86_64.abi iv) :=
  (Proof.Sha512.X86_64.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha512.X86_64.Stream.initSat] using Proof.Sha512.X86_64.Stream.initSat)

theorem update :
    Verified X86_64.target Impl.Sha512.X86_64.Stream.update (Spec.Sha512.updateContract X86_64.abi 8) :=
  Proof.Sha512.X86_64.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha512.updateContract, Spec.Sha512.updateSig, Proof.Sha512.updateX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha512.X86_64.Stream.Update.sat] using Proof.Sha512.X86_64.Stream.Update.sat)

theorem finalize :
    Verified X86_64.target Impl.Sha512.X86_64.Stream.finalize (Spec.Sha512.finalizeContract X86_64.abi 8) :=
  Proof.Sha512.X86_64.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig,
      Proof.Sha512.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha512.X86_64.Stream.Finalize.sat] using Proof.Sha512.X86_64.Stream.Finalize.sat)

end VG.Proof.Sha512.X86_64.Shared

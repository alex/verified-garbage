import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha1.X86_64.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Md
import VerifiedGarbage.Spec.Sha1.Contract

/-!
# Sha1 on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha1/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha1/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Sha1.X86_64.Shared

theorem compress :
    Verified X86_64.target Impl.Sha1.X86_64.compress (Spec.Sha1.compressContract X86_64.abi) :=
  Proof.Sha1.X86_64.compress_verified.of_implies (by
    contract_implies [Spec.Sha1.compressContract, Spec.Sha1.compressSig,
      Proof.Sha1.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha1.X86_64.satState] using Proof.Sha1.X86_64.satState)

theorem init :
    Verified X86_64.target Impl.Sha1.X86_64.Stream.init (Spec.Sha1.initContract X86_64.abi) :=
  Proof.Sha1.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha1.initContract, Spec.Sha1.initSig, Proof.Sha1.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha1.X86_64.Stream.initSat] using Proof.Sha1.X86_64.Stream.initSat)

theorem update :
    Verified X86_64.target Impl.Sha1.X86_64.Stream.update (Spec.Sha1.updateContract X86_64.abi 8) :=
  Proof.Sha1.X86_64.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha1.updateContract, Spec.Sha1.updateSig, Proof.Sha1.updateX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha1.X86_64.Stream.Update.sat,
        MdStream.X86_64.Update.sat, Impl.Sha1.X86_64.Stream.params] using Proof.Sha1.X86_64.Stream.Update.sat)

theorem finalize :
    Verified X86_64.target Impl.Sha1.X86_64.Stream.finalize (Spec.Sha1.finalizeContract X86_64.abi 8) :=
  Proof.Sha1.X86_64.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Sha1.finalizeContract, Spec.Sha1.finalizeSig,
      Proof.Sha1.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha1.X86_64.Stream.Finalize.sat,
        MdStream.X86_64.Finalize.sat, Impl.Sha1.X86_64.Stream.params] using Proof.Sha1.X86_64.Stream.Finalize.sat)

end VG.Proof.Sha1.X86_64.Shared

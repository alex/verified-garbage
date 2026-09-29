import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Md5.AArch64.Compress
import VerifiedGarbage.Proof.Md5.AArch64.Stream.Init
import VerifiedGarbage.Proof.Md5.AArch64.Stream.Md
import VerifiedGarbage.Spec.Md5.Contract

/-!
# Md5 on AArch64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Md5/AArch64/Compress.lean`); these theorems move
them to the shared contracts of `Spec/Md5/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Md5.AArch64.Shared

theorem compress :
    Verified AArch64.target Impl.Md5.AArch64.compress (Spec.Md5.compressContract AArch64.abi) :=
  Proof.Md5.AArch64.compress_verified.of_implies (by
    sig_implies [Spec.Md5.compressContract, Spec.Md5.compressSig,
      Proof.Md5.compressAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Md5.AArch64.satState] using Proof.Md5.AArch64.satState)

theorem init :
    Verified AArch64.target Impl.Md5.AArch64.Stream.init (Spec.Md5.initContract AArch64.abi) :=
  Proof.Md5.AArch64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Md5.initContract, Spec.Md5.initSig, Proof.Md5.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Md5.AArch64.Stream.initSat] using Proof.Md5.AArch64.Stream.initSat)

theorem update :
    Verified AArch64.target Impl.Md5.AArch64.Stream.update (Spec.Md5.updateContract AArch64.abi 16) :=
  Proof.Md5.AArch64.Stream.Update.update_verified.of_implies (by
    sig_implies [Spec.Md5.updateContract, Spec.Md5.updateSig, Proof.Md5.updateAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Md5.AArch64.Stream.Update.sat,
        MdStream.AArch64.Update.sat, Impl.Md5.AArch64.Stream.params] using Proof.Md5.AArch64.Stream.Update.sat)

theorem finalize :
    Verified AArch64.target Impl.Md5.AArch64.Stream.finalize (Spec.Md5.finalizeContract AArch64.abi 16) :=
  Proof.Md5.AArch64.Stream.Finalize.finalize_verified.of_implies (by
    sig_implies [Spec.Md5.finalizeContract, Spec.Md5.finalizeSig,
      Proof.Md5.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Md5.AArch64.Stream.Finalize.sat,
        MdStream.AArch64.Finalize.sat, Impl.Md5.AArch64.Stream.params] using Proof.Md5.AArch64.Stream.Finalize.sat)

end VG.Proof.Md5.AArch64.Shared

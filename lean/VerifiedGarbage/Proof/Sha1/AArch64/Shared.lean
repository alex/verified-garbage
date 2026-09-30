import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha1.AArch64.Compress
import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Md
import VerifiedGarbage.Spec.Sha1.Contract

/-!
# Sha1 on AArch64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha1/AArch64/Compress.lean`); these theorems move
them to the shared contracts of `Spec/Sha1/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Sha1.AArch64.Shared

theorem compress_of {code : Prog AArch64.isa}
    (hv : Verified AArch64.target code Proof.Sha1.compressAArch64) :
    Verified AArch64.target code (Spec.Sha1.compressContract AArch64.abi) :=
  hv.of_implies (by
    sig_implies [Spec.Sha1.compressContract, Spec.Sha1.compressSig,
      Proof.Sha1.compressAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sha1.AArch64.satState] using Proof.Sha1.AArch64.satState)

theorem init :
    Verified AArch64.target Impl.Sha1.AArch64.Stream.init (Spec.Sha1.initContract AArch64.abi) :=
  Proof.Sha1.AArch64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha1.initContract, Spec.Sha1.initSig, Proof.Sha1.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha1.AArch64.Stream.initSat] using Proof.Sha1.AArch64.Stream.initSat)

theorem update_of {code : Prog AArch64.isa}
    (hv : Verified AArch64.target code Proof.Sha1.updateAArch64) :
    Verified AArch64.target code (Spec.Sha1.updateContract AArch64.abi 16) :=
  hv.of_implies (by
    sig_implies [Spec.Sha1.updateContract, Spec.Sha1.updateSig, Proof.Sha1.updateAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha1.AArch64.Stream.Update.sat,
        MdStream.AArch64.Update.sat, Impl.Sha1.AArch64.Stream.params] using Proof.Sha1.AArch64.Stream.Update.sat)

theorem finalize_of {code : Prog AArch64.isa}
    (hv : Verified AArch64.target code Proof.Sha1.finalizeAArch64) :
    Verified AArch64.target code (Spec.Sha1.finalizeContract AArch64.abi 16) :=
  hv.of_implies (by
    sig_implies [Spec.Sha1.finalizeContract, Spec.Sha1.finalizeSig,
      Proof.Sha1.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sha1.AArch64.Stream.Finalize.sat,
        MdStream.AArch64.Finalize.sat, Impl.Sha1.AArch64.Stream.params] using Proof.Sha1.AArch64.Stream.Finalize.sat)

theorem compress :
    Verified AArch64.target Impl.Sha1.AArch64.compress (Spec.Sha1.compressContract AArch64.abi) :=
  compress_of Proof.Sha1.AArch64.compress_verified

theorem update :
    Verified AArch64.target Impl.Sha1.AArch64.Stream.update (Spec.Sha1.updateContract AArch64.abi 16) :=
  update_of Proof.Sha1.AArch64.Stream.Update.update_verified

theorem finalize :
    Verified AArch64.target Impl.Sha1.AArch64.Stream.finalize (Spec.Sha1.finalizeContract AArch64.abi 16) :=
  finalize_of Proof.Sha1.AArch64.Stream.Finalize.finalize_verified

end VG.Proof.Sha1.AArch64.Shared

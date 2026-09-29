import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86.Stream.Update
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Sha512 on X86: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha512/X86/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha512/Contract.lean`, which the
artifacts are emitted with. `update` and `finalize` call the compression
function, using the 20 bytes below the return address.
-/

namespace VG.Proof.Sha512.X86.Shared

theorem compress :
    Verified X86.target Impl.Sha512.X86.compress (Spec.Sha512.compressContract X86.abi) :=
  Proof.Sha512.X86.Compress.compress_verified.of_implies (by
    contract_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig, Proof.Sha512.compressX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha512.X86.Compress.satState, Proof.Sha512.X86.Compress.satMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using Proof.Sha512.X86.Compress.satState)

theorem init (iv : Spec.Sha512.HashValue) :
    Verified X86.target (Impl.Sha512.X86.Stream.init iv) (Spec.Sha512.initContract X86.abi iv) :=
  (Proof.Sha512.X86.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha512.X86.Stream.initSat, Proof.Sha512.X86.Stream.initSatMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using Proof.Sha512.X86.Stream.initSat)

theorem update :
    Verified X86.target Impl.Sha512.X86.Stream.update (Spec.Sha512.updateContract X86.abi 20) :=
  Proof.Sha512.X86.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha512.updateContract, Spec.Sha512.updateSig, Proof.Sha512.updateX86,
      Proof.Sha512.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha512.X86.Stream.Update.sat, Proof.Sha512.X86.Stream.Update.satMem, X86.arg, X86.argAddr,
      Mem.readW, Mem.read] using Proof.Sha512.X86.Stream.Update.sat)

theorem finalize :
    Verified X86.target Impl.Sha512.X86.Stream.finalize (Spec.Sha512.finalizeContract X86.abi 20) :=
  Proof.Sha512.X86.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, Proof.Sha512.finalizeX86,
      Proof.Sha512.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha512.X86.Stream.Finalize.sat, Proof.Sha512.X86.Stream.Finalize.satMem, X86.arg, X86.argAddr,
      Mem.readW, Mem.read] using Proof.Sha512.X86.Stream.Finalize.sat)

end VG.Proof.Sha512.X86.Shared

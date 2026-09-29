import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
import VerifiedGarbage.Spec.Sha256.Contract

/-!
# Sha256 on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha256/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha256/Contract.lean`, which the
artifacts are emitted with. `update` and `finalize` hold for any
implementation `f` of the compression function.
-/

namespace VG.Proof.Sha256.X86_64.Shared

theorem compress :
    Verified X86_64.target Impl.Sha256.X86_64.compress (Spec.Sha256.compressContract X86_64.abi) :=
  Proof.Sha256.X86_64.compress_verified.of_implies (by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig,
      Proof.Sha256.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.satState] using Proof.Sha256.X86_64.satState)

theorem compress_shani :
    Verified X86_64.target Impl.Sha256.X86_64.ShaNi.compress (Spec.Sha256.compressContract X86_64.abi) :=
  Proof.Sha256.X86_64.ShaNi.compress_verified.of_implies (by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig,
      Proof.Sha256.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.satState] using Proof.Sha256.X86_64.satState)

theorem init :
    Verified X86_64.target Impl.Sha256.X86_64.Stream.init (Spec.Sha256.initContract X86_64.abi) :=
  Proof.Sha256.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.initSat] using Proof.Sha256.X86_64.Stream.initSat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- `update`, for any compression function `f` (see `Variant.lean`). -/
theorem update {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha256.X86_64.Stream.update f) (Spec.Sha256.updateContract X86_64.abi 8) :=
  (Proof.Sha256.X86_64.Stream.Update.verified_of hf (by
    simp only [Impl.Sha256.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
      Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressAt, Code.allInstrs, hm,
      Bool.true_and]
    decide +kernel)).of_implies (by
    contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Proof.Sha256.updateX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.Update.sat,
        MdStream.X86_64.Update.sat, Impl.Sha256.X86_64.Stream.params] using Proof.Sha256.X86_64.Stream.Update.sat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem update_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha256.X86_64.Stream.update f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha256.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressAt, Code.all, h,
    Bool.true_and]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- `finalize`, for any compression function `f` (see `Variant.lean`). -/
theorem finalize {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha256.X86_64.Stream.finalize f)
      (Spec.Sha256.finalizeContract X86_64.abi 8) :=
  (Proof.Sha256.X86_64.Stream.Finalize.verified_of hf (by
    simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
      Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Code.allInstrs, hm, Bool.true_and]
    decide +kernel)).of_implies (by
    contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig,
      Proof.Sha256.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.Finalize.sat,
        MdStream.X86_64.Finalize.sat, Impl.Sha256.X86_64.Stream.params] using Proof.Sha256.X86_64.Stream.Finalize.sat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha256.X86_64.Stream.finalize f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Code.all, h, Bool.true_and]
  decide +kernel

end VG.Proof.Sha256.X86_64.Shared

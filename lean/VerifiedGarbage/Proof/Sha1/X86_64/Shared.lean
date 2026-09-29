import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha1.X86_64.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Md
import VerifiedGarbage.Spec.Sha1.Contract

/-!
# Sha1 on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha1/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha1/Contract.lean`, which the
artifacts are emitted with. `update` and `finalize` hold for any
implementation `f` of the compression function.
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

theorem compress_shani :
    Verified X86_64.target Impl.Sha1.X86_64.ShaNi.compress (Spec.Sha1.compressContract X86_64.abi) :=
  Proof.Sha1.X86_64.ShaNi.compress_verified.of_implies (by
    contract_implies [Spec.Sha1.compressContract, Spec.Sha1.compressSig,
      Proof.Sha1.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha1.X86_64.satState] using Proof.Sha1.X86_64.satState)

theorem updateImplies : Proof.Sha1.updateX86_64.Implies (Spec.Sha1.updateContract X86_64.abi 8) := by
  contract_implies [Spec.Sha1.updateContract, Spec.Sha1.updateSig, Proof.Sha1.updateX86_64,
    X86_64.abi, X86_64.argRegs]
    [Proof.Sha1.X86_64.Stream.Update.sat,
      MdStream.X86_64.Update.sat, Impl.Sha1.X86_64.Stream.params] using Proof.Sha1.X86_64.Stream.Update.sat

theorem finalizeImplies :
    Proof.Sha1.finalizeX86_64.Implies (Spec.Sha1.finalizeContract X86_64.abi 8) := by
  contract_implies [Spec.Sha1.finalizeContract, Spec.Sha1.finalizeSig,
    Proof.Sha1.finalizeX86_64, X86_64.abi, X86_64.argRegs]
    [Proof.Sha1.X86_64.Stream.Finalize.sat,
      MdStream.X86_64.Finalize.sat, Impl.Sha1.X86_64.Stream.params] using Proof.Sha1.X86_64.Stream.Finalize.sat

open VG.Impl.Sha1.X86_64.Stream (Callee) in
/-- `update`, for any compression function `f` (see `Variant.lean`). -/
theorem update {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha1.X86_64.Stream.update f) (Spec.Sha1.updateContract X86_64.abi 8) :=
  (Proof.Sha1.X86_64.Stream.Update.verified_of hf (by
    simp only [Impl.Sha1.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
      Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressAt, Code.allInstrs, hm,
      Bool.true_and]
    decide +kernel)).of_implies updateImplies

open VG.Impl.Sha1.X86_64.Stream (Callee) in
theorem update_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha1.X86_64.Stream.update f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha1.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressAt, Code.all, h,
    Bool.true_and]
  decide +kernel

open VG.Impl.Sha1.X86_64.Stream (Callee) in
/-- `finalize`, for any compression function `f` (see `Variant.lean`). -/
theorem finalize {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha1.X86_64.Stream.finalize f)
      (Spec.Sha1.finalizeContract X86_64.abi 8) :=
  (Proof.Sha1.X86_64.Stream.Finalize.verified_of hf (by
    simp only [Impl.Sha1.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
      Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Code.allInstrs, hm, Bool.true_and]
    decide +kernel)).of_implies finalizeImplies

open VG.Impl.Sha1.X86_64.Stream (Callee) in
theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha1.X86_64.Stream.finalize f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha1.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Code.all, h, Bool.true_and]
  decide +kernel

end VG.Proof.Sha1.X86_64.Shared

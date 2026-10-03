import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Md5.X86_64.Compress
import VerifiedGarbage.Proof.Md5.X86_64.Avx512.Compress
import VerifiedGarbage.Proof.Md5.X86_64.Stream.Init
import VerifiedGarbage.Proof.Md5.X86_64.Stream.Md
import VerifiedGarbage.Spec.Md5.Contract

/-!
# MD5 on x86-64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Md5/X86_64/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Md5/Contract.lean`, which the artifacts are emitted with.
`update` and `finalize` hold for any implementation `f` of the compression
function.
-/

namespace VG.Proof.Md5.X86_64.Shared

theorem compress :
    Verified X86_64.target Impl.Md5.X86_64.compress (Spec.Md5.compressContract X86_64.abi) :=
  Proof.Md5.X86_64.compress_verified.of_implies (by
    sig_implies [Spec.Md5.compressContract, Spec.Md5.compressSig,
      Proof.Md5.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Md5.X86_64.satState] using Proof.Md5.X86_64.satState)

theorem init :
    Verified X86_64.target Impl.Md5.X86_64.Stream.init (Spec.Md5.initContract X86_64.abi) :=
  Proof.Md5.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Md5.initContract, Spec.Md5.initSig, Proof.Md5.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Md5.X86_64.Stream.initSat] using Proof.Md5.X86_64.Stream.initSat)

theorem compress_avx512 :
    Verified X86_64.target Impl.Md5.X86_64.Avx512.compress (Spec.Md5.compressContract X86_64.abi) :=
  Proof.Md5.X86_64.Avx512.compress_verified.of_implies (by
    sig_implies [Spec.Md5.compressContract, Spec.Md5.compressSig,
      Proof.Md5.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Md5.X86_64.satState] using Proof.Md5.X86_64.satState)

theorem updateImplies : Proof.Md5.updateX86_64.Implies (Spec.Md5.updateContract X86_64.abi 8) := by
  sig_implies [Spec.Md5.updateContract, Spec.Md5.updateSig, Proof.Md5.updateX86_64,
    X86_64.abi, X86_64.argRegs]
    [Proof.Md5.X86_64.Stream.Update.sat,
      MdStream.X86_64.Update.sat, Impl.Md5.X86_64.Stream.params] using Proof.Md5.X86_64.Stream.Update.sat

theorem finalizeImplies :
    Proof.Md5.finalizeX86_64.Implies (Spec.Md5.finalizeContract X86_64.abi 8) := by
  sig_implies [Spec.Md5.finalizeContract, Spec.Md5.finalizeSig,
    Proof.Md5.finalizeX86_64, X86_64.abi, X86_64.argRegs]
    [Proof.Md5.X86_64.Stream.Finalize.sat,
      MdStream.X86_64.Finalize.sat, Impl.Md5.X86_64.Stream.params] using Proof.Md5.X86_64.Stream.Finalize.sat

open VG.Impl.Md5.X86_64.Stream (Callee) in
/-- `update`, for any compression function `f` (see `Variant.lean`). -/
theorem update {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Md5.X86_64.Stream.update f) (Spec.Md5.updateContract X86_64.abi 8) :=
  (Proof.Md5.X86_64.Stream.Update.verified_of hf (by
    simp only [Impl.Md5.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
      Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm,
      Bool.true_and]
    decide +kernel)).of_implies updateImplies

open VG.Impl.Md5.X86_64.Stream (Callee) in
theorem update_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Md5.X86_64.Stream.update f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Md5.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith, Code.all, h,
    Bool.true_and]
  decide +kernel

open VG.Impl.Md5.X86_64.Stream (Callee) in
/-- `finalize`, for any compression function `f` (see `Variant.lean`). -/
theorem finalize {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Md5.X86_64.Stream.finalize f)
      (Spec.Md5.finalizeContract X86_64.abi 8) :=
  (Proof.Md5.X86_64.Stream.Finalize.verified_of hf (by
    simp only [Impl.Md5.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
      Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm, Bool.true_and]
    decide +kernel)).of_implies finalizeImplies

open VG.Impl.Md5.X86_64.Stream (Callee) in
theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Md5.X86_64.Stream.finalize f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Md5.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Code.all, h, Bool.true_and]
  decide +kernel

end VG.Proof.Md5.X86_64.Shared

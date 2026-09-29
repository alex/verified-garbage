import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Hmac.X86_64.Finalize
import VerifiedGarbage.Proof.Hmac.X86_64.Init
import VerifiedGarbage.Proof.Sha256.X86_64.Shared
import VerifiedGarbage.Spec.Hmac.Contract

/-!
# Hmac on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Hmac/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Hmac/Contract.lean`, which the
artifacts are emitted with. They hold for any implementation `f` of the
compression function (see `Proof/Sha256/X86_64/Variant.lean`).
-/

namespace VG.Proof.Hmac.X86_64.Shared

open VG.Impl.Sha256.X86_64.Stream (Callee)

/-- `init`, calling any compression function `f`. -/
theorem init {f : Callee} (hf : f.Ok) (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Hmac.X86_64.init f) (Spec.Hmac.initSha256Contract X86_64.abi 8) :=
  (Proof.Hmac.X86_64.Init.verified_of hf (by
    simp only [Impl.Hmac.X86_64.init, Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hm,
      Bool.true_and, Bool.and_true]
    decide +kernel)).of_implies (by
    contract_implies [Spec.Hmac.initSha256Contract, Spec.Hmac.initSha256Sig,
      Proof.Hmac.initSha256X86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Hmac.X86_64.Init.sat] using Proof.Hmac.X86_64.Init.sat)

theorem init_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Hmac.X86_64.init f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Hmac.X86_64.init, Impl.Sha256.X86_64.Stream.compressAt, Code.all, h, Bool.true_and]
  decide +kernel

/-- `finalize`, calling the SHA-256 finalization `name` made with any
compression function `f`. -/
theorem finalize {f : Callee} (hf : f.Ok) (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
    (name : String) :
    Verified X86_64.target (Impl.Hmac.X86_64.finalize f name)
      (Spec.Hmac.finalizeSha256Contract X86_64.abi 16) :=
  (Proof.Hmac.X86_64.Finalize.verified_of hf (by
    simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.Sha256.X86_64.Stream.finalizeBody,
      Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hm, Bool.true_and]
    decide +kernel) name).of_implies (by
    contract_implies [Spec.Hmac.finalizeSha256Contract, Spec.Hmac.finalizeSha256Sig,
      Proof.Hmac.finalizeSha256X86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Hmac.X86_64.Finalize.sat] using Proof.Hmac.X86_64.Finalize.sat)

theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true)
    (name : String) :
    (Impl.Hmac.X86_64.finalize f name).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Hmac.X86_64.finalize, Impl.Hmac.X86_64.sha256Finalize, Code.all,
    Proof.Sha256.X86_64.Shared.finalize_spSafe h, Bool.and_true]
  decide +kernel

end VG.Proof.Hmac.X86_64.Shared

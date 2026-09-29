import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.X86_64.IterateCT
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC-SHA-256 on X86_64: the shared contract

Untrusted: everything here is checked by Lean. The proof is written against
a per-target contract (`Proof/Pbkdf2/X86_64/Contract.lean`); this theorem
moves it to the shared contract of `Spec/Pbkdf2/Contract.lean`, which the
artifact is emitted with. They hold for any implementation `f` of the
compression function.
-/

namespace VG.Proof.Pbkdf2.X86_64.Shared

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem iterate {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Pbkdf2.X86_64.iterate f)
      (Spec.Pbkdf2.iterateSha256Contract X86_64.abi 8) :=
  (Proof.Pbkdf2.X86_64.Iterate.verified_of hf (by
    simp only [Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
      Impl.Pbkdf2.X86_64.compressBlock, Code.allInstrs, hm, Bool.and_true]
    decide +kernel) (Proof.Pbkdf2.X86_64.Iterate.constantTime hf)).of_implies (by
    contract_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig,
      Proof.Pbkdf2.iterateSha256X86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Pbkdf2.X86_64.Iterate.sat] using Proof.Pbkdf2.X86_64.Iterate.sat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem iterate_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Pbkdf2.X86_64.iterate f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Code.all, h, Bool.and_true]
  decide +kernel

end VG.Proof.Pbkdf2.X86_64.Shared

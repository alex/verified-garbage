import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Iterate
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC-SHA-256 on X86_64: the shared contract

Untrusted: everything here is checked by Lean. The proof is written against
a per-target contract (`Proof/Pbkdf2/X86_64/Contract.lean`); this theorem
moves it to the shared contract of `Spec/Pbkdf2/Contract.lean`, which the
artifact is emitted with.
-/

namespace VG.Proof.Pbkdf2.X86_64.Shared

theorem iterate :
    Verified X86_64.target Impl.Pbkdf2.X86_64.iterate (Spec.Pbkdf2.iterateSha256Contract X86_64.abi 8) :=
  Proof.Pbkdf2.X86_64.Iterate.iterate_verified.of_implies (by
    contract_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig,
      Proof.Pbkdf2.iterateSha256X86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Pbkdf2.X86_64.Iterate.sat] using Proof.Pbkdf2.X86_64.Iterate.sat)

end VG.Proof.Pbkdf2.X86_64.Shared

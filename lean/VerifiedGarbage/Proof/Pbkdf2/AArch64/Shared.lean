import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC-SHA-256 on AArch64: the shared contract

Untrusted: everything here is checked by Lean. The proof is written against
a per-target contract (`Proof/Pbkdf2/AArch64/Contract.lean`); this theorem
moves it to the shared contract of `Spec/Pbkdf2/Contract.lean`, which the
artifact is emitted with. The function uses no stack: `bl` leaves the return
address in `x30`, which it saves in `scratch`.
-/

namespace VG.Proof.Pbkdf2.AArch64.Shared

theorem iterate :
    Verified AArch64.target Impl.Pbkdf2.AArch64.iterate (Spec.Pbkdf2.iterateSha256Contract AArch64.abi) :=
  Proof.Pbkdf2.AArch64.iterate_verified.of_implies (by
    contract_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig,
      Proof.Pbkdf2.iterateSha256AArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Pbkdf2.AArch64.sat] using Proof.Pbkdf2.AArch64.sat)

end VG.Proof.Pbkdf2.AArch64.Shared

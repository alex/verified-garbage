import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Derive.CT
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC-SHA-256 on AArch64: the shared contract

Untrusted: everything here is checked by Lean. The proof is written against
a per-target contract (`Proof/Pbkdf2/AArch64/Contract.lean`); this theorem
moves it to the shared contract of `Spec/Pbkdf2/Contract.lean`, which the
artifact is emitted with. The iteration uses no stack: `bl` leaves the return
address in `x30`, which it saves in `scratch`. The whole derivation uses 48
bytes: its own frame, and the two that `vg_hmac_sha256_finalize` and the
`vg_sha256_finalize` it calls push.
-/

namespace VG.Proof.Pbkdf2.AArch64.Shared

theorem iterate :
    Verified AArch64.target Impl.Pbkdf2.AArch64.iterate (Spec.Pbkdf2.iterateSha256Contract AArch64.abi) :=
  Proof.Pbkdf2.AArch64.iterate_verified.of_implies (by
    contract_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig,
      Proof.Pbkdf2.iterateSha256AArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Pbkdf2.AArch64.sat] using Proof.Pbkdf2.AArch64.sat)

/-- The whole of PBKDF2-HMAC-SHA-256. -/
theorem derive :
    Verified AArch64.target Impl.Pbkdf2.AArch64.derive (Spec.Pbkdf2.pbkdf2Sha256Contract AArch64.abi 48) :=
  Proof.Pbkdf2.AArch64Derive.verified.of_implies (by
    contract_implies [Spec.Pbkdf2.pbkdf2Sha256Contract, Spec.Pbkdf2.pbkdf2Sha256Sig,
      Proof.Pbkdf2.pbkdf2Sha256AArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Pbkdf2.AArch64Derive.sat] using Proof.Pbkdf2.AArch64Derive.sat)

end VG.Proof.Pbkdf2.AArch64.Shared

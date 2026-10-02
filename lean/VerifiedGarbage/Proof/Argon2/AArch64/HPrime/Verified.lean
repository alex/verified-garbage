import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.CT

/-! # Verified ARM64 H′ for every supplied BLAKE2b backend -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem verified (v : Backend) :
    Verified AArch64.target (code v.hash) (Spec.Argon2.hPrimeContract AArch64.abi 16) :=
  Verified.of_correct (code_correct v) (code_ct v) contract_implies

theorem spSafe (v : Backend) : (code v.hash).all (fun i => !isa.writesSp i) = true := by
  induction code v.hash <;> simp_all [Code.all]

end VG.Proof.Argon2.AArch64.HPrime

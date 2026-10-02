import VerifiedGarbage.Proof.Argon2.AArch64.DeriveCorrect
import VerifiedGarbage.Proof.Argon2.AArch64.DeriveCT
import VerifiedGarbage.Proof.Argon2.AArch64.DeriveContract

/-! Complete ARM64 Argon2 verification against the reviewed shared API contract. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem verified (v : HPrime.Backend) (name : String) :
    Verified AArch64.target (Impl.Argon2.AArch64.Derive.code name v.hash)
      (Spec.Argon2.deriveContract AArch64.abi 400) :=
  ⟨code_correct v name, code_ct v name, contract_sat⟩

theorem code_spSafe (v : HPrime.Backend) (name : String) :
    (Impl.Argon2.AArch64.Derive.code name v.hash).all (fun i => !isa.writesSp i) = true := by
  induction Impl.Argon2.AArch64.Derive.code name v.hash <;> simp_all [Code.all]
end VG.Proof.Argon2.AArch64.Derive

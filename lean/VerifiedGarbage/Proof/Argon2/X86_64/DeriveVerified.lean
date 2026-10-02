import VerifiedGarbage.Proof.Argon2.X86_64.DeriveCorrect
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveCT
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveContract
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveSpSafe

/-! Complete Argon2 verification against the reviewed shared API contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem verified (v : Proof.Blake2.X86_64.Backend) (name : String) :
    Verified X86_64.target (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v))
      (Spec.Argon2.deriveContract X86_64.abi 344) :=
  ⟨code_correct v name, code_ct v name, contract_sat⟩

end VG.Proof.Argon2.X86_64.Derive

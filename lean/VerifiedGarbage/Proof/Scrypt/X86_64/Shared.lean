import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Scrypt.X86_64.Salsa
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scrypt on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Scrypt/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Scrypt/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Scrypt.X86_64.Shared

theorem salsa :
    Verified X86_64.target Impl.Scrypt.X86_64.salsa (Spec.Scrypt.salsaContract X86_64.abi) :=
  Proof.Scrypt.X86_64.salsa_verified.of_implies (by
    contract_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig,
      Proof.Scrypt.salsaX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Scrypt.X86_64.satState] using Proof.Scrypt.X86_64.satState)

end VG.Proof.Scrypt.X86_64.Shared

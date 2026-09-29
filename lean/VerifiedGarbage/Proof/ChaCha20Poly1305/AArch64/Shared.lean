import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Verified
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on AArch64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/ChaCha20Poly1305/AArch64/Contract.lean`); these
theorems move them to the shared contracts of
`Spec/ChaCha20Poly1305/Contract.lean`, which the artifacts are emitted with.
The functions use no stack: their calls (`bl`) store their return addresses
in `x30`, which they save in the context.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Shared

theorem «seal» :
    Verified AArch64.target Impl.ChaCha20Poly1305.AArch64.«seal»
      (Spec.ChaCha20Poly1305.sealContract AArch64.abi) :=
  Proof.ChaCha20Poly1305.AArch64.seal_verified.of_implies (by
    contract_implies [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Proof.ChaCha20Poly1305.sealAArch64, Proof.ChaCha20Poly1305.preAArch64,
      Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.ChaCha20Poly1305.AArch64.sat] using Proof.ChaCha20Poly1305.AArch64.sat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem «open» :
    Verified AArch64.target Impl.ChaCha20Poly1305.AArch64.«open»
      (Spec.ChaCha20Poly1305.openContract AArch64.abi) :=
  Proof.ChaCha20Poly1305.AArch64.open_verified.of_implies
    { pre := by
        implies_pre [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_unfold [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig, AArch64.abi,
          AArch64.argRegs]
        simp only [Proof.ChaCha20Poly1305.openAArch64] at h
        -- The two `decrypt` terms are equal only up to unfolding numerals.
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact h
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact h
      pub := by
        implies_pub [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs,
          Proof.ChaCha20Poly1305.AArch64.sat] using Proof.ChaCha20Poly1305.AArch64.sat }

end VG.Proof.ChaCha20Poly1305.AArch64.Shared

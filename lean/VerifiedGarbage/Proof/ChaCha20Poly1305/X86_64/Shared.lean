import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on x86-64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/ChaCha20Poly1305/X86_64/Contract.lean`); these
theorems move them to the shared contracts of
`Spec/ChaCha20Poly1305/Contract.lean`, which the artifacts are emitted with.
The functions' calls store return addresses in the 16 bytes below the stack
pointer (their own calls, and those of `vg_chacha20_xor`).
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Shared

theorem «seal» :
    Verified X86_64.target Impl.ChaCha20Poly1305.X86_64.«seal»
      (Spec.ChaCha20Poly1305.sealContract X86_64.abi 16) :=
  Proof.ChaCha20Poly1305.X86_64.seal_verified.of_implies (by
    contract_implies [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Proof.ChaCha20Poly1305.sealX86_64, Proof.ChaCha20Poly1305.preX86_64,
      Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.ChaCha20Poly1305.X86_64.sat] using Proof.ChaCha20Poly1305.X86_64.sat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem «open» :
    Verified X86_64.target Impl.ChaCha20Poly1305.X86_64.«open»
      (Spec.ChaCha20Poly1305.openContract X86_64.abi 16) :=
  Proof.ChaCha20Poly1305.X86_64.open_verified.of_implies
    { pre := by
        implies_pre [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_unfold [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig, X86_64.abi,
          X86_64.argRegs]
        simp only [Proof.ChaCha20Poly1305.openX86_64] at h
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
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.argRegs,
          Proof.ChaCha20Poly1305.X86_64.sat] using Proof.ChaCha20Poly1305.X86_64.sat }

end VG.Proof.ChaCha20Poly1305.X86_64.Shared

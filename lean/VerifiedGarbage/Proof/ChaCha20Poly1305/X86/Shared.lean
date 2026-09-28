import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Verified
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on x86 (32-bit): the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/ChaCha20Poly1305/X86/Contract.lean`); these
theorems move them to the shared contracts of
`Spec/ChaCha20Poly1305/Contract.lean`, which the artifacts are emitted with.
The functions' calls use the 32 bytes of stack below the return address: a
frame of up to four arguments and a return address, and, for
`vg_chacha20_xor`, the 12 bytes its own calls use.
-/

namespace VG.Proof.ChaCha20Poly1305.X86.Shared

/-- The return value, `eax`, is the low half of `edx:eax`. -/
theorem low32 (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow]
  simp [Nat.mod_eq_of_lt this]

theorem «seal» :
    Verified X86.target Impl.ChaCha20Poly1305.X86.«seal» (Spec.ChaCha20Poly1305.sealContract X86.abi 32) :=
  Proof.ChaCha20Poly1305.X86.seal_verified.of_implies (by
    contract_implies [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Proof.ChaCha20Poly1305.sealX86, Proof.ChaCha20Poly1305.preX86, Proof.ChaCha20Poly1305.pubX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.ChaCha20Poly1305.X86.sat, Proof.ChaCha20Poly1305.X86.satMem, X86.arg, X86.argAddr, Mem.readW,
        Mem.read] using Proof.ChaCha20Poly1305.X86.sat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem «open» :
    Verified X86.target Impl.ChaCha20Poly1305.X86.«open» (Spec.ChaCha20Poly1305.openContract X86.abi 32) :=
  Proof.ChaCha20Poly1305.X86.open_verified.of_implies
    { pre := by
        implies_pre [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86, Proof.ChaCha20Poly1305.preX86,
          Proof.ChaCha20Poly1305.pubX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by
        intro s s' _ h
        sig_unfold [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig, X86.abi,
          X86.argSlots, X86.argVal, X86.argBytes]
        simp only [Proof.ChaCha20Poly1305.openX86] at h
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact ⟨by rw [h.1]; exact low32 _ _, h.2⟩
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => rw [h]; exact low32 _ _
      pub := by
        implies_pub [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86, Proof.ChaCha20Poly1305.preX86,
          Proof.ChaCha20Poly1305.pubX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86, Proof.ChaCha20Poly1305.preX86,
          Proof.ChaCha20Poly1305.pubX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
          Proof.ChaCha20Poly1305.X86.sat, Proof.ChaCha20Poly1305.X86.satMem, X86.arg, X86.argAddr,
          Mem.readW, Mem.read] using Proof.ChaCha20Poly1305.X86.sat }

end VG.Proof.ChaCha20Poly1305.X86.Shared

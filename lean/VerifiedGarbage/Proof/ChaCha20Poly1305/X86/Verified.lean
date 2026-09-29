import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on x86 (32-bit): `Verified`

Untrusted: everything here is checked by Lean. Correctness (from
`Correct.lean`), constant time (from `CT.lean`), and a state satisfying the
precondition.
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86

/-- Memory whose five argument slots (at `0x5004`) hold `0x1000`, `0x2000`,
`0`, `0x3000` and `0`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5009 then 0x20 else if a = 0x5011 then 0x30 else 0

/-- A state satisfying the precondition (with no additional data and no
data). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x3000, 0⟩, ⟨0x5004, 20⟩]

theorem seal_ok (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.X86.«seal» s t s' ∧ abiPreserved s s' ∧
      sealX86.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := seal_correct (APre.of s hs)
  exact ⟨t, s', he, h, hpost⟩

theorem open_ok (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.X86.«open» s t s' ∧ abiPreserved s s' ∧
      openX86.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := open_correct (APre.of s hs)
  exact ⟨t, s', he, h, hpost⟩

/-- The return value, `eax`, is the low half of `edx:eax`. -/
theorem low32 (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow]
  simp [Nat.mod_eq_of_lt this]

theorem seal_verified :
    Verified X86.target Impl.ChaCha20Poly1305.X86.«seal»
      (Spec.ChaCha20Poly1305.sealContract X86.abi 32) :=
  Verified.of_correct seal_ok seal_ct (by
    have a0 : arg sat 0 = 0x1000 := by decide
    have a1 : arg sat 1 = 0x2000 := by decide
    have a2 : arg sat 2 = 0 := by decide
    have a3 : arg sat 3 = 0x3000 := by decide
    have a4 : arg sat 4 = 0 := by decide
    have e : argAddr sat 0 = 0x5004 := by decide
    have esp : sat.gpr .esp = 0x5000 := rfl
    sig_implies [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Proof.ChaCha20Poly1305.sealX86, Proof.ChaCha20Poly1305.preX86, Proof.ChaCha20Poly1305.pubX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, e, esp] using sat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem open_verified :
    Verified X86.target Impl.ChaCha20Poly1305.X86.«open»
      (Spec.ChaCha20Poly1305.openContract X86.abi 32) :=
  Verified.of_correct open_ok open_ct
    { pre := by
        sig_implies_pre [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86, Proof.ChaCha20Poly1305.preX86,
          Proof.ChaCha20Poly1305.pubX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by
        intro s s' _ h
        sig_eval [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig, X86.abi,
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
        sig_implies_pub [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86, Proof.ChaCha20Poly1305.preX86,
          Proof.ChaCha20Poly1305.pubX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        have a0 : arg sat 0 = 0x1000 := by decide
        have a1 : arg sat 1 = 0x2000 := by decide
        have a2 : arg sat 2 = 0 := by decide
        have a3 : arg sat 3 = 0x3000 := by decide
        have a4 : arg sat 4 = 0 := by decide
        have e : argAddr sat 0 = 0x5004 := by decide
        have esp : sat.gpr .esp = 0x5000 := rfl
        sig_implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86, Proof.ChaCha20Poly1305.preX86,
          Proof.ChaCha20Poly1305.pubX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a1, a2, a3, a4, e, esp] using sat }

end VG.Proof.ChaCha20Poly1305.X86

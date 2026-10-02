import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# scrypt on x86-64: PBKDF2-HMAC-SHA256 as a callee

Untrusted: everything here is checked by Lean. `vg_pbkdf2_hmac_sha256` (any
implementation of it) is verified against the shared contract
`VG.Spec.Hmac.sha256I.pbkdf2Contract`; its caller works with the same
contract spelt out (`pbkG`, the contract its proof is written against):
`pbk_correct` and `pbk_ct` are its correctness and constant time under
`pbkG`, from its `Verified` proof.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (pbkG)

/-- `pbkdf2`'s contract, spelt out. -/
abbrev pbkK : Contract isa := pbkG Spec.Hmac.sha256S 200

theorem map_range2 {α : Type} (f : Nat → α) : List.map f (List.range 2) = [f 0, f 1] := rfl

theorem pbk_pre {s : State} (h : pbkK.pre s) :
    (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi 24).pre s := by
  simp only [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    X86_64.abi, X86_64.argRegs, map_range2, List.append_eq]
  sig_pre [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    X86_64.abi, X86_64.argRegs, map_range2, List.append_eq]
  simp only [pbkK, pbkG, Spec.Hmac.sha256S] at h
  sig_split h
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega

theorem pbk_post {s s' : State} (h : (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi 24).post s s') :
    pbkK.post s s' := by
  simp only [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch] at h
  sig_post [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    X86_64.abi, X86_64.argRegs, map_range2, List.append_eq] at h
  exact h

theorem pbk_pub {s₁ s₂ : State} (h : pbkK.pub s₁ s₂) :
    (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi 24).pub s₁ s₂ := by
  simp only [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pub [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    X86_64.abi, X86_64.argRegs, map_range2, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h9, h1, h2, h3, h4, h5, h6, h7, h8⟩

variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi 24))
include hv

theorem pbk_correct (s : State) (h : pbkK.pre s) :
    ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (pbk_pre h)
  exact ⟨t, s', he, ha, pbk_post hp⟩

theorem pbk_ct : ConstantTime isa pbkK.pre pbkK.pub pbk :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => hv.2.1 _ _ _ _ _ _ (pbk_pre h₁) (pbk_pre h₂) (pbk_pub hp) e₁ e₂

end VG.Proof.Scrypt.X86_64.Whole

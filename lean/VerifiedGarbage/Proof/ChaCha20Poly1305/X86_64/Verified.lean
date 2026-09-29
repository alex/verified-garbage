import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness (from
`Correct.lean`), constant time (from `CT.lean`), and a state satisfying the
precondition, for any implementation `v` of `vg_chacha20_xor`.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64

/-- A state satisfying the precondition (with no additional data and no
data). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x3000, 0⟩]

theorem seal_mxcsr (v : Proof.ChaCha20.X86_64.XorImpl) :
    («seal» v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», crypt, Code.allInstrs, v.mxcsr]
  decide +kernel

theorem open_mxcsr (v : Proof.ChaCha20.X86_64.XorImpl) :
    («open» v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«open», crypt, Code.allInstrs, v.mxcsr]
  decide +kernel

/-- `seal` and `open` never write the stack pointer. -/
theorem seal_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    («seal» v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», crypt, Code.all, v.spSafe]
  decide +kernel

theorem open_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    («open» v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«open», crypt, Code.all, v.spSafe]
  decide +kernel

theorem seal_ok (v : Proof.ChaCha20.X86_64.XorImpl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callee) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := seal_correct v (APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mxcsr v) he h, hpost⟩

theorem seal_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem open_ok (v : Proof.ChaCha20.X86_64.XorImpl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callee) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := open_correct v (APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (open_mxcsr v) he h, hpost⟩

theorem open_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa openX86_64.pre openX86_64.pub («open» v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem seal_verified (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target («seal» v.callee) (Spec.ChaCha20Poly1305.sealContract X86_64.abi 24) :=
  Verified.of_correct (seal_ok v) (seal_ct v) (by
    sig_implies [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Proof.ChaCha20Poly1305.sealX86_64, Proof.ChaCha20Poly1305.preX86_64,
      Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.ChaCha20Poly1305.X86_64.sat] using Proof.ChaCha20Poly1305.X86_64.sat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem open_verified (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target («open» v.callee) (Spec.ChaCha20Poly1305.openContract X86_64.abi 24) :=
  Verified.of_correct (open_ok v) (open_ct v)
    { pre := by
        sig_implies_pre [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig, X86_64.abi,
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
        sig_implies_pub [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.argRegs]
          [Proof.ChaCha20Poly1305.X86_64.sat] using Proof.ChaCha20Poly1305.X86_64.sat }

end VG.Proof.ChaCha20Poly1305.X86_64

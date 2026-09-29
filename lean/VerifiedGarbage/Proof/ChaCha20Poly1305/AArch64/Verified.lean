import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness (from
`Correct.lean`), constant time, and a state satisfying the precondition.

The taint analysis runs through the callees' code: it knows `x21`–`x25`
(the context, the data, the additional data and their lengths) for public
after each call because no callee writes them (unlike `x19` and `x20`, which
`vg_chacha20_xor` restores from memory, and which the analysis therefore
treats as secret afterwards).
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64

/-- The public registers on entry: the pointers and the lengths. -/
def τ₀ : VG.AArch64.Taint.T := VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]

theorem agree₀ {s₁ s₂ : State} (hpub : pubAArch64 s₁ s₂) : VG.AArch64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [τ₀, VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with no additional data and no
data). -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x3000, 0⟩]

theorem seal_ok (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.AArch64.«seal» s t s' ∧ abiPreserved s s' ∧
      sealAArch64.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := seal_correct (APre.of s hs)
  exact ⟨t, s', he, h, hpost⟩

theorem seal_ct : ConstantTime isa sealAArch64.pre sealAArch64.pub
    Impl.ChaCha20Poly1305.AArch64.«seal» :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

theorem open_ok (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.AArch64.«open» s t s' ∧ abiPreserved s s' ∧
      openAArch64.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := open_correct (APre.of s hs)
  exact ⟨t, s', he, h, hpost⟩

theorem open_ct : ConstantTime isa openAArch64.pre openAArch64.pub
    Impl.ChaCha20Poly1305.AArch64.«open» :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

theorem seal_verified :
    Verified AArch64.target Impl.ChaCha20Poly1305.AArch64.«seal»
      (Spec.ChaCha20Poly1305.sealContract AArch64.abi) :=
  Verified.of_correct seal_ok seal_ct (by
    sig_implies [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Proof.ChaCha20Poly1305.sealAArch64, Proof.ChaCha20Poly1305.preAArch64,
      Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.ChaCha20Poly1305.AArch64.sat] using Proof.ChaCha20Poly1305.AArch64.sat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem open_verified :
    Verified AArch64.target Impl.ChaCha20Poly1305.AArch64.«open»
      (Spec.ChaCha20Poly1305.openContract AArch64.abi) :=
  Verified.of_correct open_ok open_ct
    { pre := by
        sig_implies_pre [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig, AArch64.abi,
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
        sig_implies_pub [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
          [Proof.ChaCha20Poly1305.AArch64.sat] using Proof.ChaCha20Poly1305.AArch64.sat }

end VG.Proof.ChaCha20Poly1305.AArch64

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Correct
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness (from
`Correct.lean`), constant time, and a state satisfying the precondition.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64

/-- The public registers and what is known about memory on entry: the lengths
of the context and the data (the data's varies) and the registers holding
their bases. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [1024, 0],
    bases := [(.rdi, 0, 0), (.rcx, 1, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : preX86_64 s₁) (h₂ : preX86_64 s₂) (hpub : pubX86_64 s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, preX86_64 s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d], by simp [hw, (s.gpr .r8).isLt.le]⟩, fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p4, p5]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

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

theorem seal_ok (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.X86_64.«seal» s t s' ∧ abiPreserved s s' ∧
      sealX86_64.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := seal_correct (APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h, hpost⟩

theorem seal_ct : ConstantTime isa sealX86_64.pre sealX86_64.pub
    Impl.ChaCha20Poly1305.X86_64.«seal» :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem open_ok (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.X86_64.«open» s t s' ∧ abiPreserved s s' ∧
      openX86_64.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := open_correct (APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h, hpost⟩

theorem open_ct : ConstantTime isa openX86_64.pre openX86_64.pub
    Impl.ChaCha20Poly1305.X86_64.«open» :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem seal_verified :
    Verified X86_64.target Impl.ChaCha20Poly1305.X86_64.«seal»
      (Spec.ChaCha20Poly1305.sealContract X86_64.abi 16) :=
  Verified.of_correct seal_ok seal_ct (by
    sig_implies [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Proof.ChaCha20Poly1305.sealX86_64, Proof.ChaCha20Poly1305.preX86_64,
      Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.ChaCha20Poly1305.X86_64.sat] using Proof.ChaCha20Poly1305.X86_64.sat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem open_verified :
    Verified X86_64.target Impl.ChaCha20Poly1305.X86_64.«open»
      (Spec.ChaCha20Poly1305.openContract X86_64.abi 16) :=
  Verified.of_correct open_ok open_ct
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

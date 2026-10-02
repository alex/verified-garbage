import VerifiedGarbage.Proof.X25519.X86_64.Main
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# X25519 on x86-64: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter),
satisfiability, and the shared contract of `Spec/`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_ok (s : State) (hs : Proof.X25519.x25519X86_64.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86_64.x25519 s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct baseline_ok (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem x25519_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre Proof.X25519.x25519X86_64.pub
    Impl.X25519.X86_64.x25519 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem x25519_verified :
    Verified X86_64.target Impl.X25519.X86_64.x25519 (Spec.X25519.x25519Contract X86_64.abi) :=
  Verified.of_correct x25519_ok x25519_ct (by
    sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs,
      Proof.X25519.x25519X86_64] [satState] using satState)

end VG.Proof.X25519.X86_64

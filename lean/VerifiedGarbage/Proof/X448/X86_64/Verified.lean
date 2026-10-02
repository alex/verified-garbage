import VerifiedGarbage.Proof.X448.X86_64.Main
import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# X448 on x86-64: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter),
satisfiability, and the shared contract of `Spec/`.
-/

namespace VG.Proof.X448.X86_64

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
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448X86_64.pre s) :
    ∃ t s', Exec isa Impl.X448.X86_64.x448 s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem x448_ct : ConstantTime isa Proof.X448.x448X86_64.pre Proof.X448.x448X86_64.pub
    Impl.X448.X86_64.x448 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem x448_verified :
    Verified X86_64.target Impl.X448.X86_64.x448 (Spec.X448.x448Contract X86_64.abi) :=
  Verified.of_correct x448_ok x448_ct (by
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, X86_64.abi, X86_64.argRegs,
      Proof.X448.x448X86_64] [satState] using satState)

end VG.Proof.X448.X86_64

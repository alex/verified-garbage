import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X448.X86_64.Verified

/-!
# X448 on x86-64 with BMI2 and ADX: `Verified`

The proof of `vg_x448` (`Proof/X448/X86_64/Verified.lean`) for the field
multiplications `adx` (`adx_ok`): correctness from `correct`, constant time by
taint tracking (the only branches are on the loop counters, and every address
is an argument plus a constant or a counter), satisfiability, and the shared
contract.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64

theorem x448Adx_ok (s : State) (hs : Proof.X448.x448X86_64.pre s) :
    ∃ t s', Exec isa Impl.X448.X86_64.x448Adx s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct adx_ok (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem x448Adx_ct : ConstantTime isa Proof.X448.x448X86_64.pre Proof.X448.x448X86_64.pub
    Impl.X448.X86_64.x448Adx := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem x448Adx_verified :
    Verified X86_64.target Impl.X448.X86_64.x448Adx (Spec.X448.x448Contract X86_64.abi) :=
  Verified.of_correct x448Adx_ok x448Adx_ct (by
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, X86_64.abi, X86_64.argRegs,
      Proof.X448.x448X86_64] [satState] using satState)

end VG.Proof.X448.X86_64

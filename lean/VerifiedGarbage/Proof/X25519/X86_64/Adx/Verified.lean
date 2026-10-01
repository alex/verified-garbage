import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Verified

/-!
# X25519 on x86-64 with BMI2 and ADX: `Verified`

Untrusted: everything here is checked by Lean. The proof of `vg_x25519`
(`Proof/X25519/X86_64/Verified.lean`) for the field multiplications `adx`
(`adx_ok`): correctness from `correct`, constant time by taint tracking (the
only branches are on the loop counters, and every address is an argument plus
a constant or a counter), satisfiability, and the shared contract.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64

theorem x25519Adx_ok (s : State) (hs : Proof.X25519.x25519X86_64.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86_64.x25519Adx s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct adx_ok (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem x25519Adx_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre
    Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519Adx := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem x25519Adx_verified :
    Verified X86_64.target Impl.X25519.X86_64.x25519Adx (Spec.X25519.x25519Contract X86_64.abi) :=
  Verified.of_correct x25519Adx_ok x25519Adx_ct (by
    sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs,
      Proof.X25519.x25519X86_64] [satState] using satState)

end VG.Proof.X25519.X86_64

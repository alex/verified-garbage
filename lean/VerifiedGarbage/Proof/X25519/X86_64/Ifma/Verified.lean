import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Ladder
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# X25519 on x86-64 with AVX512_IFMA: `Verified`

The proof of `vg_x25519` (`Proof/X25519/X86_64/Main.lean`) with the ladder
`vladder` (`vladder_ok`) and the field multiplications `adx` for the
inversion: correctness from `correct_of`; MXCSR's control bits kept, as the
ladder loads MXCSR only between saving it in `r11` and loading it back
(`ctlOk`); constant time by taint tracking (the only branches are on the loop
counters, and every address is an argument plus a constant or a counter);
satisfiability, and the shared contract.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64

theorem vladder_post {s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe} (h : LPre base k u s) :
    WP isa Impl.X25519.X86_64.Ifma.vladder s (LPost base k u s) :=
  Ifma.vladder_ok h.scr h.bits h.x1 h.swap

theorem x25519Ifma_ok (s : State) (hs : Proof.X25519.x25519X86_64.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86_64.x25519Ifma s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct_of adx_ok vladder_post (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_ctl (by lit_decide) he h.1, h.2⟩

theorem x25519Ifma_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre
    Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519Ifma := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem x25519Ifma_verified :
    Verified X86_64.target Impl.X25519.X86_64.x25519Ifma (Spec.X25519.x25519Contract X86_64.abi) :=
  Verified.of_correct x25519Ifma_ok x25519Ifma_ct (by
    sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs,
      Proof.X25519.x25519X86_64] [satState] using satState)

end VG.Proof.X25519.X86_64

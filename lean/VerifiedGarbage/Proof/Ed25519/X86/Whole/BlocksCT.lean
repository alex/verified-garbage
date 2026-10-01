import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! Blocks whose memory addresses depend only on ESP, and functional facts
retained while composing their equal-leakage proofs. -/
namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86

theorem block_rel {P : State → State → Prop} {is : List Instr}
    (he : ∀ a b, P a b → a.gpr .esp = b.gpr .esp)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block is) hint).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => by
    rw [List.mem_singleton.mp hr]; exact he a b h) ht

theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun a b => F a ∧ F' b) c fun _ _ => True)
    (ha : ∀ a, F a → WP isa c a G) (hb : ∀ b, F' b → WP isa c b G') :
    RelCT isa (fun a b => F a ∧ F' b) c fun a b => G a ∧ G' b :=
  (hct.wp fun a b h => ⟨ha a h.1, hb b h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Ed25519.X86.Whole

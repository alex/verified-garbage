import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! Equal traces for straight-line helpers addressed through the public SP. -/
namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64

theorem block_rel {P : State → State → Prop} {is : List Instr}
    (he : ∀ a b, P a b → a.sp = b.sp)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (VG.AArch64.Taint.ofRegs []) (.block is) hint).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [])
    (fun a b h => ⟨he a b h, fun r hr => by simp at hr⟩) ht

theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun a b => F a ∧ F' b) c fun _ _ => True)
    (ha : ∀ a, F a → WP isa c a G) (hb : ∀ b, F' b → WP isa c b G') :
    RelCT isa (fun a b => F a ∧ F' b) c fun a b => G a ∧ G' b :=
  (hct.wp fun a b h => ⟨ha a h.1, hb b h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Ed25519.AArch64.Whole

import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Body
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def Two (L : Lay) (g₁ g₂ : Reg → BitVec 32)
    (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b ∧ P a ∧ P b

theorem two_sp {P : State → Prop} {a b : State} (h : Two L g₁ g₂ m₁ m₂ P a b) :
    a.sp = b.sp := h.1.sp.trans h.2.1.sp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ m₁ t → P t → WP isa c t fun u => Ctx L g₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ m₂ t → P t → WP isa c t fun u => Ctx L g₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) c (Two L g₁ g₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

def AllArgs (L : Lay) (args : List (Reg × Value)) (stack : List Value) (s : State) : Prop :=
  OutArgs L args s ∧ StackArgs L stack s

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (stack : List Value) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, valid p.2) (hs : stack.length ≤ 6)
    (hvs : ∀ v ∈ stack, valid v) (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stack))
      (Two L g₁ g₂ m₁ m₂ (AllArgs L args stack)) := by
  refine two_wp ((Whole.setup_ct args stack).mono (fun _ _ h => two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro s hc _
    exact WP.mono (args_ok hc hL ha hn hv hs hvs hr) fun _ ⟨hu, _, hg, ht⟩ => ⟨hu, hg, ht⟩
  · intro s hc _
    exact WP.mono (args_ok hc hL hb hn hv hs hvs hr) fun _ ⟨hu, _, hg, ht⟩ => ⟨hu, hg, ht⟩

theorem args_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : Two L g₁ g₂ m₁ m₂ (AllArgs L args stack) a b) {p : Reg × Value} (hp : p ∈ args) :
    a.gpr p.1 = b.gpr p.1 := (h.2.2.1.1 p hp).trans (h.2.2.2.1 p hp).symm

theorem call_gpr_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : Two L g₁ g₂ m₁ m₂ (AllArgs L args stack) a b) {p : Reg × Value}
    (hp : p ∈ args) (hl : p.1 ∉ linkRegs) : a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := by
  rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl]
  exact args_eq h hp

theorem stack_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : Two L g₁ g₂ m₁ m₂ (AllArgs L args stack) a b) {j : Nat} (hj : j < stack.length) :
    stackArg a j = stackArg b j := (h.2.2.1.2 j hj).trans (h.2.2.2.2 j hj).symm

theorem call_ct {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hn : c.noFrames = true)
    (ready : ∀ {g m t}, Ctx L g m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, Two L g₁ g₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) (.call name c)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply two_wp
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.1
    let rb := ready h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := Whole.CallReady.covers_state h.1 ra
    obtain ⟨cb, wb⟩ := Whole.CallReady.covers_state h.2.1 rb
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb⟩
  · intro t hc hs
    exact WP.mono (Whole.CallReady.wp hc (ready hc hs) correct hn) fun _ hu => ⟨hu, trivial⟩
  · intro t hc hs
    exact WP.mono (Whole.CallReady.wp hc (ready hc hs) correct hn) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.Arm.VerifyMessage

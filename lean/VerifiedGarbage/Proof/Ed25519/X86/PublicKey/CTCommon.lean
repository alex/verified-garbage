import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.CTReady

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86.Whole (Value setup)

def Two (s₁ s₂ : State) (P : State → State → Prop) (a b : State) : Prop :=
  Ctx s₁ a ∧ Ctx s₂ b ∧ P s₁ a ∧ P s₂ b

variable {s₁ s₂ : State}

theorem esp_eq (pub : pkLocal.pub s₁ s₂) : esp s₁ = esp s₂ := congrArg (· - BitVec.ofNat 32 256) pub.1

theorem argValue_eq (pub : pkLocal.pub s₁ s₂) {v : Value} (hv : Whole.valid 3 v) : argValue s₁ v = argValue s₂ v := by
  cases v with
  | const _ => rfl
  | frame d => exact congrArg (· + BitVec.ofNat 32 d) (esp_eq pub)
  | caller i d =>
    apply congrArg (· + BitVec.ofNat 32 d)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by change i < 3 at hv; omega) with rfl | rfl | rfl
    · exact pub.2.1
    · exact pub.2.2.1
    · exact pub.2.2.2

theorem two_esp (pub : pkLocal.pub s₁ s₂) {P : State → State → Prop} {a b : State} (h : Two s₁ s₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.esp.trans ((esp_eq pub).trans h.2.1.esp.symm)

theorem two_wp (h₁ : Facts s₁) (h₂ : Facts s₂) {P Q : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two s₁ s₂ P) c fun _ _ => True)
    (hw : ∀ s t, Facts s → Ctx s t → P s t → WP isa c t fun u => Ctx s u ∧ Q s u) :
    RelCT isa (Two s₁ s₂ P) c (Two s₁ s₂ Q) :=
  (hct.wp fun a b h => ⟨hw s₁ a h₁ h.1 h.2.2.1, hw s₂ b h₂ h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) (vs : List Value) (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0 vs)) hint).isSome = true) :
    RelCT isa (Two s₁ s₂ fun _ _ => True) (.block (setup 0 vs)) (Two s₁ s₂ (Slots vs)) :=
  two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) ht) fun _ _ h hc _ =>
    WP.mono (setup_ok h hc hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem call_args_eq (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {a b : State} (h : Two s₁ s₂ (Slots vs) a b) {j : Nat} (hj : j < vs.length) :
    arg a.callEntry j = arg b.callEntry j := by
  rw [Whole.call_arg h.1.esp h₁.toBounds.call (by have := h₁.toBounds.frame; omega) (by omega),
    Whole.call_arg h.2.1.esp h₂.toBounds.call (by have := h₂.toBounds.frame; omega) (by omega),
    h.2.2.1 j hj, h.2.2.2 j hj]
  exact argValue_eq pub (hv _ (List.getElem_mem hj))

theorem call_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (sp : NoSp c) (stack : stackUse c ≤ 20)
    (ready : ∀ {s t : State}, Facts s → Ctx s t → Slots vs s t →
      Whole.CallReady k (esp s) (pkRd s) (pkWr s) t)
    (kp : ∀ (a b : State) ar aw br bw, a.gpr .esp = b.gpr .esp →
      (∀ j < vs.length, arg a.callEntry j = arg b.callEntry j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two s₁ s₂ (Slots vs)) (.call name c) (Two s₁ s₂ fun _ _ => True) := by
  apply two_wp h₁ h₂
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h₁ h.1 h.2.2.1
    let rb := ready h₂ h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (two_esp pub h) (fun _ hj => call_args_eq h₁ h₂ pub hn hv h hj),
      ca, wa, cb, wb, two_esp pub h⟩
  · intro s t h hc hs
    exact WP.mono ((ready h hc hs).wp hc correct sp stack h.toBounds.call) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.X86.PublicKey

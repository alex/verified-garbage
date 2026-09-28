import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Taint tracking for AArch64

Untrusted: everything here is checked by Lean.

The abstract state is the list of registers known to be public. Memory is
always secret: a loaded value is secret, and an address must be computed from
public registers. (No modelled instruction touches the flags.)
-/

namespace VG.AArch64.Taint

deriving instance Lean.ToExpr for Reg

abbrev T := List Reg

def pub (τ : T) (r : Reg) : Bool := τ.contains r

def Agree (τ : T) (s₁ s₂ : State) : Prop := ∀ r ∈ τ, s₁.gpr r = s₂.gpr r

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : T :=
  if p then r :: τ else τ.filter (· != r)

def step (τ : T) : Instr → Option T
  | .add _ d n m | .sub _ d n m | .logic _ _ d n m => some (set τ d (pub τ n && pub τ m))
  | .addImm _ d n _ | .subImm _ d n _ | .ror _ d n _ | .lsr _ d n _ | .rev32 d n | .rev d n =>
    some (set τ d (pub τ n))
  | .movz _ d _ _ => some (set τ d true)
  | .movk _ d _ _ => some (set τ d (pub τ d))
  | .ldr _ t n _ | .ldrb t n _ => if pub τ n then some (set τ t false) else none
  | .str _ _ n _ | .strb _ n _ => if pub τ n then some τ else none

def condPub (τ : T) : Cond → Bool
  | .zero _ r | .nonzero _ r => pub τ r

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ := by simp [pub]

theorem Agree.reg {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) :
    s₁.gpr r = s₂.gpr r := h r (pub_iff.mp hr)

theorem Agree.read {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true)
    (sz : Size) : s₁.read sz r = s₂.read sz r := by
  simp [State.read, h.reg hr]

theorem Agree.write {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) (sz : Size) (d : Reg) {p : Bool}
    {v₁ v₂ : BitVec sz.bits} (hv : p = true → v₁ = v₂) :
    Agree (set τ d p) (s₁.write sz d v₁) (s₂.write sz d v₂) := by
  intro r hr
  simp only [State.write]
  unfold set at hr
  by_cases hp : p = true
  · simp only [hp, ite_true, List.mem_cons] at hr
    by_cases hrd : r = d
    · simp [hrd, hv hp]
    · simp [hrd, h r (hr.resolve_left hrd)]
  · simp only [hp, Bool.false_eq_true, ite_false, List.mem_filter, bne_iff_ne, ne_eq] at hr
    simp [hr.2, h r hr.1]

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | add sz d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨rfl, ha.write sz d fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.read hp.1, ha.read hp.2]
  | sub sz d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨rfl, ha.write sz d fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.read hp.1, ha.read hp.2]
  | logic op sz d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨rfl, ha.write sz d fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.read hp.1, ha.read hp.2]
  | addImm sz d n imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h; simp only [h, ite_true, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write sz d fun hp => by rw [ha.read hp]⟩
  | subImm sz d n imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h; simp only [h, ite_true, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write sz d fun hp => by rw [ha.read hp]⟩
  | ror sz d n sh =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h; simp only [h, ite_true, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write sz d fun hp => by rw [ha.read hp]⟩
  | lsr sz d n sh =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h; simp only [h, ite_true, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write sz d fun hp => by rw [ha.read hp]⟩
  | rev32 d n =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write .w d fun hp => by rw [ha.read hp]⟩
  | rev d n =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write .x d fun hp => by rw [ha.read hp]⟩
  | movz sz d imm hw =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h; simp only [h, ite_true, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write sz d fun _ => rfl⟩
  | movk sz d imm hw =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h; simp only [h, ite_true, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write sz d fun hp => by rw [ha.read hp]⟩
  | ldr sz t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, -, v₁, -, rfl⟩ := e₁; obtain ⟨a₂, -, v₂, -, rfl⟩ := e₂
    exact ha.write sz t fun h => by cases h
  | str sz t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, State.store] at e₁ e₂
    obtain ⟨a₁, -, e₁⟩ := e₁; obtain ⟨a₂, -, e₂⟩ := e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ha
  | ldrb t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, -, v₁, -, rfl⟩ := e₁; obtain ⟨a₂, -, v₂, -, rfl⟩ := e₂
    exact ha.write .w t fun h => by cases h
  | strb t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, State.store] at e₁ e₂
    obtain ⟨a₁, -, e₁⟩ := e₁; obtain ⟨a₂, -, e₂⟩ := e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ha

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : condPub τ c = true) : eval c s₁ = eval c s₂ := by
  cases c <;> simp only [condPub] at hc <;> simp [eval, ha.read hc]

end VG.AArch64.Taint

namespace VG.AArch64

/-- Taint tracking for AArch64. -/
def taint : VG.Taint isa where
  T := Taint.T
  Agree := Taint.Agree
  step := Taint.step
  step_sound := Taint.step_sound
  condPub := Taint.condPub
  cond_sound := Taint.cond_sound
  meet τ₁ τ₂ := τ₁.filter (Taint.pub τ₂)
  meet_left h r hr := h r (List.mem_filter.mp hr).1
  meet_right h r hr := h r (Taint.pub_iff.mp (List.mem_filter.mp hr).2)
  le τ σ := τ.all (Taint.pub σ)
  le_sound hle h r hr := h r (Taint.pub_iff.mp (List.all_eq_true.mp hle r hr))
  -- A call leaves unknown values in `x16`, `x17` and `x30`; a return changes nothing.
  call τ := some (τ.filter fun r => r != .x16 && r != .x17 && r != .x30)
  call_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at hr
    obtain ⟨hr, ⟨h16, h17⟩, h30⟩ := hr
    simp only [h16, h17, h30, ite_false]
    exact h r hr
  ret τ := some τ
  ret_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, h⟩

end VG.AArch64

import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.TCB.AArch64.Target
import Mathlib.Tactic.Set

/-!
# Taint tracking for AArch64

Untrusted: everything here is checked by Lean.

The abstract state is the set of registers known to be public; the stack
pointer is always public. Memory is always secret: a loaded value is secret,
and an address must be computed from public registers or the stack pointer.
The vector registers are always secret too: a value moved from one to a
general-purpose register (`umov`) is secret. (No modelled instruction
touches the flags.)
-/

namespace VG.AArch64.Taint

deriving instance Lean.ToExpr for Reg

instance : RegIdx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

abbrev T := RegSet Reg

def pub (τ : T) (r : Reg) : Bool := τ.mem r

/-- Exactly the registers `rs` are public. -/
def ofRegs (rs : List Reg) : T := RegSet.ofList rs

@[simp] theorem mem_ofRegs {rs : List Reg} {r : Reg} : r ∈ ofRegs rs ↔ r ∈ rs := RegSet.mem_ofList

def Agree (τ : T) (s₁ s₂ : State) : Prop := s₁.sp = s₂.sp ∧ ∀ r ∈ τ, s₁.gpr r = s₂.gpr r

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : T :=
  if p then τ.insert r else τ.erase r

def step (τ : T) : Instr → Option T
  | .add _ d n m | .sub _ d n m | .logic _ _ d n m | .mul _ d n m =>
    some (set τ d (pub τ n && pub τ m))
  | .madd _ d n m a => some (set τ d (pub τ n && pub τ m && pub τ a))
  | .addImm _ d n _ | .subImm _ d n _ | .ror _ d n _ | .lsr _ d n _ | .lsl _ d n _ | .rev32 d n
  | .rev d n => some (set τ d (pub τ n))
  | .movz _ d _ _ => some (set τ d true)
  | .movk _ d _ _ => some (set τ d (pub τ d))
  | .ldr _ t n _ | .ldrb t n _ => if pub τ n then some (set τ t false) else none
  -- The stack pointer is public, and memory secret.
  | .ldrSp t _ => some (set τ t false)
  | .str _ _ n _ | .strb _ n _ => if pub τ n then some τ else none
  | .vop _ => some τ
  | .ldrq _ n _ | .strq _ n _ => if pub τ n then some τ else none
  | .umov _ d _ _ => some (set τ d false)
  -- Frames are not analysed yet.
  | .push .. | .pop .. => none

def condPub (τ : T) : Cond → Bool
  | .zero _ r | .nonzero _ r => pub τ r

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ := Iff.rfl

theorem Agree.reg {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) :
    s₁.gpr r = s₂.gpr r := h.2 r (pub_iff.mp hr)

theorem Agree.read {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true)
    (sz : Size) : s₁.read sz r = s₂.read sz r := by
  simp [State.read, h.reg hr]

theorem Agree.write {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) (sz : Size) (d : Reg) {p : Bool}
    {v₁ v₂ : BitVec sz.bits} (hv : p = true → v₁ = v₂) :
    Agree (set τ d p) (s₁.write sz d v₁) (s₂.write sz d v₂) := by
  refine ⟨h.1, fun r hr => ?_⟩
  simp only [State.write]
  unfold set at hr
  by_cases hp : p = true
  · simp only [hp, ite_true, RegSet.mem_insert] at hr
    by_cases hrd : r = d
    · simp [hrd, hv hp]
    · simp [hrd, h.2 r (hr.resolve_left hrd)]
  · simp only [hp, Bool.false_eq_true, ite_false, RegSet.mem_erase] at hr
    simp [hr.1, h.2 r hr.2]

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | push | pop => simp only [step, reduceCtorEq] at hs
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
  | lsl sz d n sh =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h; simp only [h, ite_true, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write sz d fun hp => by rw [ha.read hp]⟩
  | madd sz d n m a =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨rfl, ha.write sz d fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.read hp.1.1, ha.read hp.1.2, ha.read hp.2]
  | mul sz d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨rfl, ha.write sz d fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.read hp.1, ha.read hp.2]
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
  | ldrSp t off =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨by simp [addrs, ha.1], ?_⟩
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h; simp only [h, and_self, ite_true, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, -, rfl⟩ := e₁; obtain ⟨v₂, -, rfl⟩ := e₂
    exact ha.write .x t fun h => by cases h
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
  | vop op =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨⟨_, _⟩, -, rfl⟩ := e₁; obtain ⟨⟨_, _⟩, -, rfl⟩ := e₂
    exact ⟨rfl, ha.1, ha.2⟩
  | ldrq t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, -, v₁, -, rfl⟩ := e₁; obtain ⟨a₂, -, v₂, -, rfl⟩ := e₂
    exact ⟨ha.1, ha.2⟩
  | strq t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, State.store] at e₁ e₂
    obtain ⟨a₁, -, e₁⟩ := e₁; obtain ⟨a₂, -, e₂⟩ := e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ha
  | umov sz d n i =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h; simp only [h, ite_true, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write sz d fun h => by cases h⟩

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : condPub τ c = true) : eval c s₁ = eval c s₂ := by
  cases c <;> simp only [condPub] at hc <;> simp [eval, ha.read hc]

/-- A frame's push stores to memory, which is secret. -/
def push (τ : T) : Instr → Option T
  | .push _ => some τ
  | _ => none

/-- A frame's pop loads a secret. -/
def pop (τ : T) : Instr → Option T
  | .pop r => some (τ.erase r)
  | _ => none

theorem push_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (h : Agree τ s₁ s₂)
    (hs : push τ i = some τ') (e₁ : isa.push i s₁ = some s₁') (e₂ : isa.push i s₂ = some s₂') :
    isa.addrs i s₁ = isa.addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i <;> simp only [push, reduceCtorEq] at hs
  cases hs
  simp only [isa, AArch64.push] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  exact ⟨by simp [addrs, h.1], by simp [h.1], h.2⟩

theorem pop_sound {τ τ' : T} {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (h : Agree τ b₁ b₂)
    (hs : pop τ j = some τ') (e₁ : isa.pop j a₁ b₁ = some c₁) (e₂ : isa.pop j a₂ b₂ = some c₂) :
    isa.addrs j b₁ = isa.addrs j b₂ ∧ Agree τ' c₁ c₂ := by
  cases j <;> simp only [pop, reduceCtorEq] at hs
  rename_i r
  cases hs
  simp only [isa, AArch64.pop] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  refine ⟨by simp [addrs, h.1], by simp [h.1], fun r' hr' => ?_⟩
  simp only [RegSet.mem_erase] at hr'
  simp [State.write, hr'.1, h.2 r' hr'.2]

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
  meet τ₁ τ₂ := τ₁.inter τ₂
  meet_left h := ⟨h.1, fun r hr => h.2 r (RegSet.mem_inter.mp hr).1⟩
  meet_right h := ⟨h.1, fun r hr => h.2 r (RegSet.mem_inter.mp hr).2⟩
  le τ σ := τ.subset σ
  le_sound hle h := ⟨h.1, fun r hr => h.2 r (RegSet.mem_of_subset hle hr)⟩
  -- A call leaves unknown values in `x16`, `x17` and `x30`; a return changes nothing.
  call τ := some ((τ.erase .x16).erase .x17 |>.erase .x30)
  call_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    refine ⟨rfl, h.1, fun r hr => ?_⟩
    simp only [RegSet.mem_erase] at hr
    obtain ⟨h30, h17, h16, hr⟩ := hr
    simp only [h16, h17, h30, ite_false]
    exact h.2 r hr
  ret τ := some τ
  ret_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, h⟩
  -- A frame's push stores to memory, which is secret; its pop loads a secret.
  push := Taint.push
  push_sound := Taint.push_sound
  pop := Taint.pop
  pop_sound := Taint.pop_sound

end VG.AArch64

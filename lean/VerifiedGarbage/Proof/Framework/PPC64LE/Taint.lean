import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# Taint tracking for PPC64LE

Untrusted: everything here is checked by Lean.

The abstract state is the set of registers known to be public; the stack
pointer is always public. Memory is always secret: a loaded value is secret,
and an address must be computed from public registers or the stack pointer.
The link register is not tracked: `mflr` gives a secret. (No modelled
instruction touches the condition register outside a branch condition.)
-/

namespace VG.PPC64LE.Taint

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
  | .add d n m | .sub d n m | .logic _ d n m => some (set τ d (pub τ n && pub τ m))
  | .addi d n _ | .subi d n _ | .ori d n _ | .oris d n _ | .rotr _ d n _ | .lsr _ d n _
  | .lsl d n _ => some (set τ d (pub τ n))
  | .li d _ | .lis d _ => some (set τ d true)
  | .load _ t n _ | .lbz t n _ => if pub τ n then some (set τ t false) else none
  | .store _ _ n _ | .stb _ n _ => if pub τ n then some τ else none
  | .loadRev _ t a b => if pub τ a && pub τ b then some (set τ t false) else none
  | .storeRev _ _ a b => if pub τ a && pub τ b then some τ else none
  | .mflr d => some (set τ d false)
  | .mtlr _ => some τ
  -- Frames are analysed by `push` and `pop`.
  | .push .. | .pop .. => none

def condPub (τ : T) : Cond → Bool
  | .zero _ r | .nonzero _ r => pub τ r

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ := Iff.rfl

theorem Agree.reg {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) :
    s₁.gpr r = s₂.gpr r := h.2 r (pub_iff.mp hr)

theorem Agree.read {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true)
    (sz : Size) : s₁.read sz r = s₂.read sz r := by
  simp [State.read, h.reg hr]

theorem Agree.write {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) (d : Reg) {p : Bool}
    {v₁ v₂ : BitVec 64} (hv : p = true → v₁ = v₂) :
    Agree (set τ d p) (s₁.write d v₁) (s₂.write d v₂) := by
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

/-- The result of an instruction that writes `d` from the state, if it does
not fault. -/
theorem step_write {τ : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂) {d : Reg} {p : Bool}
    {f : State → BitVec 64} (hf : p = true → f s₁ = f s₂)
    (e₁ : s₁' = s₁.write d (f s₁)) (e₂ : s₂' = s₂.write d (f s₂)) :
    Agree (set τ d p) s₁' s₂' := by
  subst e₁ e₂; exact ha.write d hf

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | push | pop => simp only [step, reduceCtorEq] at hs
  | add d n m | sub d n m | logic op d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨rfl, ha.write d fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.reg hp.1, ha.reg hp.2]
  | addi d n imm | subi d n imm | li d imm | rotr sz d n sh | lsr sz d n sh | lsl d n sh =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    first
    | exact ⟨rfl, ha.write d fun hp => by rw [ha.reg hp]⟩
    | exact ⟨rfl, ha.write d fun hp => by rw [ha.read hp]⟩
    | exact ⟨rfl, ha.write d fun _ => rfl⟩
  | lis d imm | ori d n imm | oris d n imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    first
    | exact ⟨rfl, ha.write d fun hp => by rw [ha.reg hp]⟩
    | exact ⟨rfl, ha.write d fun _ => rfl⟩
  | mflr d =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write d fun h => by cases h⟩
  | mtlr r =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha⟩
  | load sz t n off | lbz t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, -, v₁, -, rfl⟩ := e₁; obtain ⟨a₂, -, v₂, -, rfl⟩ := e₂
    exact ha.write t fun h => by cases h
  | store sz t n off | stb t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, State.store] at e₁ e₂
    obtain ⟨a₁, -, e₁⟩ := e₁; obtain ⟨a₂, -, e₂⟩ := e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ha
  | loadRev sz t a b =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    simp only [Bool.and_eq_true] at hn
    refine ⟨by simp [addrs, ha.reg hn.1, ha.reg hn.2], ?_⟩
    cases sz <;>
    · simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨a₁, -, v₁, -, rfl⟩ := e₁; obtain ⟨a₂, -, v₂, -, rfl⟩ := e₂
      exact ha.write t fun h => by cases h
  | storeRev sz t a b =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    simp only [Bool.and_eq_true] at hn
    refine ⟨by simp [addrs, ha.reg hn.1, ha.reg hn.2], ?_⟩
    cases sz <;>
    · simp only [exec, Option.bind_eq_some_iff, State.store] at e₁ e₂
      obtain ⟨a₁, -, e₁⟩ := e₁; obtain ⟨a₂, -, e₂⟩ := e₂
      split at e₁ <;> [cases e₁; cases e₁]
      split at e₂ <;> [cases e₂; cases e₂]
      exact ha

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
  simp only [isa, PPC64LE.push] at e₁ e₂
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
  simp only [isa, PPC64LE.pop] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  refine ⟨by simp [addrs, h.1], by simp [h.1], fun r' hr' => ?_⟩
  simp only [RegSet.mem_erase] at hr'
  simp [State.write, hr'.1, h.2 r' hr'.2]

end VG.PPC64LE.Taint

namespace VG.PPC64LE

/-- Taint tracking for PPC64LE. -/
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
  -- A call leaves unknown values in `r0`, `r11` and `r12` (and `LR`, which is
  -- not tracked); a return changes nothing.
  call τ := some ((τ.erase .r0).erase .r11 |>.erase .r12)
  call_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    refine ⟨rfl, h.1, fun r hr => ?_⟩
    simp only [RegSet.mem_erase] at hr
    obtain ⟨h12, h11, h0, hr⟩ := hr
    simp only [h0, h11, h12, ite_false]
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

end VG.PPC64LE

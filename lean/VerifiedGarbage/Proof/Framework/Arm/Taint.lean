import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.TCB.Arm.Target

/-!
# Taint tracking for ARMv7

Untrusted: everything here is checked by Lean.

The abstract state is the list of registers known to be public, and whether
the flags are public. Memory is always secret: a loaded value is secret, and
an address must be computed from public registers.
-/

namespace VG.Arm.Taint

structure T where
  regs : List Reg
  flags : Bool
  deriving DecidableEq

def pub (τ : T) (r : Reg) : Bool := τ.regs.contains r

def Agree (τ : T) (s₁ s₂ : State) : Prop :=
  (∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r) ∧
  (τ.flags = true → s₁.n = s₂.n ∧ s₁.z = s₂.z ∧ s₁.c = s₂.c ∧ s₁.v = s₂.v)

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : List Reg :=
  if p then r :: τ.regs else τ.regs.filter (· != r)

def op2Pub (τ : T) : Op2 → Bool
  | .imm _ => true
  | .reg r | .shifted r _ _ => pub τ r

def step (τ : T) : Instr → Option T
  | .mov d op2 => some ⟨set τ d (op2Pub τ op2), τ.flags⟩
  | .dp _ d n op2 => some ⟨set τ d (pub τ n && op2Pub τ op2), τ.flags⟩
  | .subs d n op2 => let p := pub τ n && op2Pub τ op2; some ⟨set τ d p, p⟩
  | .cmp n op2 => some ⟨τ.regs, pub τ n && op2Pub τ op2⟩
  | .movw d _ => some ⟨set τ d true, τ.flags⟩
  | .movt d _ => some ⟨set τ d (pub τ d), τ.flags⟩
  | .rev d m => some ⟨set τ d (pub τ m), τ.flags⟩
  | .ldr t n _ => if pub τ n then some ⟨set τ t false, τ.flags⟩ else none
  | .str _ n _ => if pub τ n then some τ else none

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ.regs := by simp [pub]

theorem Agree.reg {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) :
    s₁.gpr r = s₂.gpr r := h.1 r (pub_iff.mp hr)

theorem Agree.op2 {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {o : Op2} (ho : op2Pub τ o = true) :
    o.eval s₁ = o.eval s₂ := by
  cases o with
  | imm v => rfl
  | reg r => simp only [Op2.eval, h.reg ho]
  | shifted r sh n => simp only [Op2.eval, h.reg ho]

theorem regs_set {τ : T} {s₁ s₂ : State} (h : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r)
    {d : Reg} {p : Bool} {v₁ v₂ : BitVec 32} (hv : p = true → v₁ = v₂) :
    ∀ r ∈ set τ d p, (s₁.setReg d v₁).gpr r = (s₂.setReg d v₂).gpr r := by
  intro r hr
  simp only [State.setReg]
  unfold set at hr
  by_cases hp : p = true
  · simp only [hp, ite_true, List.mem_cons] at hr
    by_cases hrd : r = d
    · simp [hrd, hv hp]
    · simp [hrd, h r (hr.resolve_left hrd)]
  · simp only [hp, Bool.false_eq_true, ite_false, List.mem_filter, bne_iff_ne, ne_eq] at hr
    simp [hr.2, h r hr.1]

theorem Agree.setReg {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) (d : Reg) {p : Bool}
    {v₁ v₂ : BitVec 32} (hv : p = true → v₁ = v₂) :
    Agree ⟨set τ d p, τ.flags⟩ (s₁.setReg d v₁) (s₂.setReg d v₂) :=
  ⟨regs_set h.1 hv, fun hf => by simpa [State.setReg] using h.2 hf⟩

theorem op2_some {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {o : Op2} {y₁ y₂ : BitVec 32}
    (e₁ : o.eval s₁ = some y₁) (e₂ : o.eval s₂ = some y₂) : op2Pub τ o = true → y₁ = y₂ :=
  fun ho => by rw [h.op2 ho, e₂] at e₁; cases e₁; rfl

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | mov d o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    exact ⟨rfl, ha.setReg d (op2_some ha h₁ h₂)⟩
  | dp op d n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨rfl, ha.setReg d fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
  | subs d n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨rfl, regs_set (fun r hr => by simpa [subFlags] using ha.1 r hr) fun hp => ?_,
      fun hp => ?_⟩ <;>
    · simp only [Bool.and_eq_true] at hp
      rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
      try simp [subFlags, State.setReg]
  | cmp n o =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, h₁, rfl⟩ := e₁; obtain ⟨y₂, h₂, rfl⟩ := e₂
    refine ⟨rfl, fun r hr => by simpa [subFlags] using ha.1 r hr, fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [op2_some ha h₁ h₂ hp.2, ha.reg hp.1]
    simp [subFlags]
  | movw d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.setReg d fun _ => rfl⟩
  | movt d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.setReg d fun hp => by rw [ha.reg hp]⟩
  | rev d m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.setReg d fun hp => by rw [ha.reg hp]⟩
  | ldr t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨x₁, -, rfl⟩ := e₁; obtain ⟨x₂, -, rfl⟩ := e₂
    exact ha.setReg t fun h => by cases h
  | str t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, State.store32] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ha

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : τ.flags = true) : eval c s₁ = eval c s₂ := by
  obtain ⟨-, hz, -, -⟩ := ha.2 hc
  cases c <;> simp [eval, hz]

end VG.Arm.Taint

namespace VG.Arm

/-- Taint tracking for ARMv7. -/
def taint : VG.Taint isa where
  T := Taint.T
  Agree := Taint.Agree
  step := Taint.step
  step_sound := Taint.step_sound
  condPub τ _ := τ.flags
  cond_sound := Taint.cond_sound
  meet τ₁ τ₂ := ⟨τ₁.regs.filter (Taint.pub τ₂), τ₁.flags && τ₂.flags⟩
  meet_left h := ⟨fun r hr => h.1 r (List.mem_filter.mp hr).1,
    fun hf => h.2 (by simp only [Bool.and_eq_true] at hf; exact hf.1)⟩
  meet_right h := ⟨fun r hr => h.1 r (Taint.pub_iff.mp (List.mem_filter.mp hr).2),
    fun hf => h.2 (by simp only [Bool.and_eq_true] at hf; exact hf.2)⟩
  le τ σ := τ.regs.all (Taint.pub σ) && (!τ.flags || σ.flags)
  le_sound {τ σ s₁ s₂} hle h := by
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hle
    refine ⟨fun r hr => h.1 r (Taint.pub_iff.mp (hle.1 r hr)), fun hf => h.2 ?_⟩
    rcases hle.2 with h' | h'
    · simp [hf] at h'
    · exact h'

/-- The taint in which exactly the registers `rs` are public. -/
def Taint.ofRegs (rs : List Reg) : Taint.T := ⟨rs, false⟩

end VG.Arm

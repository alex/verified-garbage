import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Taint tracking over memory both runs agree on (AArch64)

The taint analysis (`Proof/Framework/AArch64/Taint.lean`) treats memory as
secret. `memTaint` is one for code that runs with permissions only on
memory whose bytes two runs agree on (`MemEq`): every load it can make is
then public, and a store keeps the agreement if it stores a public value at
a public address. It proves constant time for code whose branches and
addresses depend on the contents of such memory, e.g. rejection sampling
from an output that is a function of the declared leak.

`RelCT.narrow` applies it to code that runs with more permissions but only
touches memory the two runs agree on: the runs from the states narrowed to
those regions leak what the actual runs leak (`Exec.widen` and determinism).
-/

namespace VG.AArch64.MemTaint

open VG.AArch64.Taint (T pub set)

/-- `m₁` and `m₂` agree on every byte of the regions `rs`. -/
def MemEq (rs : List Region) (m₁ m₂ : Mem) : Prop := ∀ x, InRegions rs x 1 → m₁ x = m₂ x

/-- The registers `τ` agree, and the permissions and the memory they permit. -/
def Agree (τ : T) (s₁ s₂ : State) : Prop :=
  Taint.Agree τ s₁ s₂ ∧ s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ MemEq (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

/-- Instructions that only write a general-purpose register. -/
def regOp : Instr → Bool
  | .add .. | .sub .. | .addImm .. | .subImm .. | .logic .. | .ror .. | .lsr .. | .lsl .. | .madd ..
  | .mul .. | .rev32 .. | .rev .. | .movz .. | .movk .. => true
  | _ => false

/-- Loads are public, stores must store public values; the other memory
instructions and frames are not analysed. -/
def step (τ : T) : Instr → Option T
  | .ldr _ t n _ | .ldrb t n _ => if pub τ n then some (set τ t true) else none
  | .str _ t n _ | .strb t n _ => if pub τ n && pub τ t then some τ else none
  | i => if regOp i then Taint.step τ i else none

theorem exec_regOp {i : Instr} (hi : regOp i = true) {s s' : State} (h : exec i s = some s') :
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i <;> simp [regOp] at hi <;> simp only [exec] at h <;>
    first
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)
    | (split at h <;> [skip; cases h]
       simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)

theorem MemEq.read {rs : List Region} {m₁ m₂ : Mem} (h : MemEq rs m₁ m₂) {a : Addr} {n : Nat}
    (hi : InRegions rs a n) (hn : n < 2 ^ 64) : m₁.read a n = m₂.read a n := by
  obtain ⟨r, hr, hc⟩ := hi
  exact Mem.read_congr fun i hi' =>
    h _ ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hi')⟩

theorem MemEq.write {rs : List Region} {m₁ m₂ : Mem} (h : MemEq rs m₁ m₂) (a : Addr) (n : Nat)
    (v : BitVec (8 * n)) : MemEq rs (m₁.write a n v) (m₂.write a n v) := fun x hx => by
  simp only [Mem.write]
  split
  · rfl
  · exact h x hx

theorem regOp_sound {τ τ' : T} {i : Instr} (hr : regOp i = true) {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (hs : Taint.step τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  obtain ⟨hadd, ht⟩ := Taint.step_sound ha.1 hs e₁ e₂
  obtain ⟨m₁, r₁, w₁⟩ := exec_regOp hr e₁
  obtain ⟨m₂, r₂, w₂⟩ := exec_regOp hr e₂
  exact ⟨hadd, ht, by rw [r₁, r₂, ha.2.1], by rw [w₁, w₂, ha.2.2.1], by
    rw [m₁, m₂, r₁, w₁]; exact ha.2.2.2⟩

theorem load_sound {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {n : Reg} (hn : pub τ n = true)
    (bytes off : Nat) {a₁ a₂ : Addr} (h₁ : addr s₁ bytes n off = some a₁)
    (h₂ : addr s₂ bytes n off = some a₂) {v₁ v₂ : BitVec (8 * bytes)}
    (l₁ : s₁.load a₁ bytes = some v₁) (l₂ : s₂.load a₂ bytes = some v₂) (hb : bytes < 2 ^ 64) :
    v₁ = v₂ := by
  have ea : a₁ = a₂ := by
    simp only [addr, ha.1.reg hn] at h₁ h₂
    split at h₁ <;> [rename_i hc; cases h₁]
    rw [ite_eq_left hc] at h₂
    exact (Option.some.inj h₁).symm.trans (Option.some.inj h₂)
  subst ea
  simp only [State.load] at l₁ l₂
  split at l₁ <;> [rename_i hi; cases l₁]
  split at l₂ <;> [skip; cases l₂]
  cases l₁; cases l₂
  exact ha.2.2.2.read hi hb

theorem store_sound {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {n : Reg} (hn : pub τ n = true)
    (bytes off : Nat) {a₁ a₂ : Addr} (h₁ : addr s₁ bytes n off = some a₁)
    (h₂ : addr s₂ bytes n off = some a₂) {v : BitVec (8 * bytes)} {s₁' s₂' : State}
    (e₁ : s₁.store a₁ bytes v = some s₁') (e₂ : s₂.store a₂ bytes v = some s₂') :
    Agree τ s₁' s₂' := by
  have ea : a₁ = a₂ := by
    simp only [addr, ha.1.reg hn] at h₁ h₂
    split at h₁ <;> [rename_i hc; cases h₁]
    rw [ite_eq_left hc] at h₂
    exact (Option.some.inj h₁).symm.trans (Option.some.inj h₂)
  subst ea
  simp only [State.store] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.write _ _ _⟩

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | ldr sz t n off =>
    simp only [step] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    refine ⟨by simp [addrs, ha.1.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, v₁, l₁, rfl⟩ := e₁; obtain ⟨a₂, h₂, v₂, l₂, rfl⟩ := e₂
    have hv := load_sound ha hn _ off h₁ h₂ l₁ l₂ (by cases sz <;> decide)
    subst hv
    exact ⟨ha.1.write sz t fun _ => rfl, ha.2⟩
  | ldrb t n off =>
    simp only [step] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    refine ⟨by simp [addrs, ha.1.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, v₁, l₁, rfl⟩ := e₁; obtain ⟨a₂, h₂, v₂, l₂, rfl⟩ := e₂
    have hv := load_sound ha hn _ off h₁ h₂ l₁ l₂ (by decide)
    subst hv
    exact ⟨ha.1.write .w t fun _ => rfl, ha.2⟩
  | str sz t n off =>
    simp only [step] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    simp only [Bool.and_eq_true] at hn
    refine ⟨by simp [addrs, ha.1.reg hn.1], ?_⟩
    simp only [exec, Option.bind_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, e₁⟩ := e₁; obtain ⟨a₂, h₂, e₂⟩ := e₂
    rw [ha.1.read hn.2] at e₁
    exact store_sound ha hn.1 _ off h₁ h₂ e₁ e₂
  | strb t n off =>
    simp only [step] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    simp only [Bool.and_eq_true] at hn
    refine ⟨by simp [addrs, ha.1.reg hn.1], ?_⟩
    simp only [exec, Option.bind_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, e₁⟩ := e₁; obtain ⟨a₂, h₂, e₂⟩ := e₂
    rw [ha.1.read hn.2] at e₁
    exact store_sound ha hn.1 _ off h₁ h₂ e₁ e₂
  | _ =>
    simp only [step] at hs
    split at hs <;> [rename_i hr; cases hs]
    exact regOp_sound hr ha hs e₁ e₂

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : Taint.condPub τ c = true) : eval c s₁ = eval c s₂ :=
  Taint.cond_sound ha.1 hc

end VG.AArch64.MemTaint

namespace VG.AArch64

open MemTaint in
/-- Taint tracking over memory both runs agree on, for AArch64. -/
def memTaint : VG.Taint isa where
  T := Taint.T
  Agree := MemTaint.Agree
  step := MemTaint.step
  step_sound := MemTaint.step_sound
  condPub := Taint.condPub
  cond_sound := MemTaint.cond_sound
  meet τ₁ τ₂ := τ₁.inter τ₂
  meet_left h := ⟨taint.meet_left h.1, h.2⟩
  meet_right h := ⟨taint.meet_right h.1, h.2⟩
  le τ σ := τ.subset σ
  le_sound hle h := ⟨taint.le_sound hle h.1, h.2⟩
  call _ := none
  call_sound _ hs _ _ := by cases hs
  ret _ := none
  ret_sound _ hs _ _ := by cases hs
  push _ _ := none
  push_sound _ hs _ _ := by cases hs
  pop _ _ := none
  pop_sound _ hs _ _ := by cases hs

/-- Code run with more permissions than the regions `rd` and `wr` it
touches: if the runs from the states narrowed to them exist, and those
leak the same traces, so do the actual runs. -/
theorem RelCT.narrow {c : Prog isa} {P : State → State → Prop} {Q : State → State → Prop}
    (rd wr : List Region)
    (hc : ∀ s₁ s₂, P s₁ s₂ → (Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ Covers wr s₁.wr) ∧
      (Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ Covers wr s₂.wr))
    (hw : ∀ s₁ s₂, P s₁ s₂ →
      (∃ t s', Exec isa c (s₁.withRegions rd wr) t s') ∧ ∃ t s', Exec isa c (s₂.withRegions rd wr) t s')
    (h : RelCT isa (fun u₁ u₂ => ∃ s₁ s₂, P s₁ s₂ ∧ u₁ = s₁.withRegions rd wr ∧
      u₂ = s₂.withRegions rd wr) c Q) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨⟨c₁, w₁⟩, ⟨c₂, w₂⟩⟩ := hc _ _ hp
  obtain ⟨⟨u₁, v₁, n₁⟩, ⟨u₂, v₂, n₂⟩⟩ := hw _ _ hp
  have x₁ := Exec.widen n₁ (rd := s₁.rd) (wr := s₁.wr) (by simpa using c₁) (by simpa using w₁)
  have x₂ := Exec.widen n₂ (rd := s₂.rd) (wr := s₂.wr) (by simpa using c₂) (by simpa using w₂)
  simp only [State.withRegions_withRegions, State.withRegions_self] at x₁ x₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ x₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ x₂
  exact ⟨(h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ n₁ n₂).1, trivial⟩

end VG.AArch64

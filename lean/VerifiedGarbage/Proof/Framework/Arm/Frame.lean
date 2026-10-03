import VerifiedGarbage.Proof.Framework.Arm.RelCT

/-!
# Frames (ARMv7)

A frame `push {rs}; body; ldr r, [sp], #n` stores the registers `rs` below
the stack pointer, which becomes a writable region (`pushed`), runs `body`,
and loads `r` from the frame as it removes it (`popped`). `WP.frame` runs
one; `RelCT.frame` relates two runs of one: the push and the pop leak only
addresses computed from the stack pointer, so if it is the same in both
runs, the frame leaks what its body does. (The taint analysis does not
analyse frames.)
-/

namespace VG.Arm

/-- The state after `push {rs}`. -/
def pushed (rs : List Reg) (s : State) : State :=
  { s with
    sp := s.sp - BitVec.ofNat 32 (4 * rs.length)
    mem := storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * rs.length)) (rs.map s.gpr)
    wr := ⟨State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length)), 4 * rs.length⟩ :: s.wr }

/-- The state after `ldr r, [sp], #n`. -/
def popped (r : Reg) (n : Nat) (s : State) : State :=
  { s.setReg r (s.mem.readW (State.addr s.sp) 32) with
    sp := s.sp + BitVec.ofNat 32 n, wr := s.wr.tail }

theorem push_pushed {rs : List Reg} {s : State} (hrs : regList rs = true)
    (hn : 4 * rs.length ≤ s.sp.toNat) : isa.push (.push rs) s = some (pushed rs s) := by
  simp only [isa, push, hrs, hn, and_self, ite_true]; rfl

@[simp] theorem pushed_gpr (rs : List Reg) (s : State) : (pushed rs s).gpr = s.gpr := rfl
@[simp] theorem pushed_rd (rs : List Reg) (s : State) : (pushed rs s).rd = s.rd := rfl
@[simp] theorem pushed_sp (rs : List Reg) (s : State) :
    (pushed rs s).sp = s.sp - BitVec.ofNat 32 (4 * rs.length) := rfl
@[simp] theorem pushed_wr (rs : List Reg) (s : State) :
    (pushed rs s).wr = ⟨State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length)), 4 * rs.length⟩ :: s.wr := rfl
@[simp] theorem pushed_unknowns (rs : List Reg) (s : State) : (pushed rs s).unknowns = s.unknowns := rfl

@[simp] theorem popped_rd (r : Reg) (n : Nat) (s : State) : (popped r n s).rd = s.rd := rfl
@[simp] theorem popped_wr (r : Reg) (n : Nat) (s : State) : (popped r n s).wr = s.wr.tail := rfl
@[simp] theorem popped_sp (r : Reg) (n : Nat) (s : State) :
    (popped r n s).sp = s.sp + BitVec.ofNat 32 n := rfl
@[simp] theorem popped_mem (r : Reg) (n : Nat) (s : State) : (popped r n s).mem = s.mem := rfl

theorem popped_gpr {r q : Reg} (h : q ≠ r) (n : Nat) (s : State) : (popped r n s).gpr q = s.gpr q := by
  simp [popped, State.setReg, h]

/-- A frame of the words `rs`, popped into `r`: its body runs from `pushed rs s`. -/
theorem WP.frame {rs : List Reg} {r : Reg} {body : Prog isa} {s : State} {Q : State → Prop}
    (hrs : regList rs = true) (hn : 4 * rs.length ≤ s.sp.toNat) (hlt : 4 * rs.length < 256)
    (hb : WP isa body (pushed rs s) fun s₂ => Q (popped r (4 * rs.length) s₂)) :
    WP isa (.frame (.push rs) body (.pop r (4 * rs.length))) s Q := by
  obtain ⟨t, s₂, he, hq⟩ := hb
  obtain ⟨-, hw, hsp⟩ := Exec.rdwr he
  have hpop : isa.pop (.pop r (4 * rs.length)) (pushed rs s) s₂ = some (popped r (4 * rs.length) s₂) := by
    have hc : 4 * rs.length % 4 = 0 ∧ 4 * rs.length < 256 ∧ s₂.sp = (pushed rs s).sp ∧
        s₂.wr = (pushed rs s).wr ∧
        (pushed rs s).wr.head? = some ⟨State.addr (pushed rs s).sp, 4 * rs.length⟩ :=
      ⟨Nat.mul_mod_right _ _, hlt, hsp, hw, rfl⟩
    simp only [isa, pop]
    split
    · rfl
    · exact absurd hc ‹_›
  exact ⟨_, _, Exec.frame (push_pushed hrs hn) he hpop, hq⟩

theorem push_push_sp {rs : List Reg} {s a : State} (h : isa.push (.push rs) s = some a) :
    a.sp = s.sp - BitVec.ofNat 32 (4 * rs.length) := by
  simp only [isa, push] at h; split at h <;> cases h; rfl

/-- Two runs of a frame leak the same trace if they have the same stack
pointer and the runs of its body, from the states after the push, do. -/
theorem RelCT.frame {rs : List Reg} {r : Reg} {n : Nat} {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ isa.push (.push rs) s₁ = some a ∧
      isa.push (.push rs) s₂ = some b) body fun _ _ => True) :
    RelCT isa P (.frame (.push rs) body (.pop r n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, p₁, p₂⟩ b₁ b₂
      have e := hsp _ _ hp
      have pa₁ := push_push_sp p₁
      have pa₂ := push_push_sp p₂
      have hq₁ := (pop_eq q₁).2.2.2.2.1
      have hq₂ := (pop_eq q₂).2.2.2.2.1
      refine ⟨?_, trivial⟩
      rw [ht]
      simp only [addrs, hq₁, hq₂, pa₁, pa₂, e]

end VG.Arm

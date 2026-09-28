import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Calls and frames (x86, 32-bit)

Untrusted: everything here is checked by Lean.

A call (`Code.call`) stores its return address at `esp - 4` and runs the
called function from there (`State.callEntry`). `WP.call` runs a call of
verified code without calls or frames of its own from the callee's
`Verified` proof, as `WP.inline` does for inlined code.

A frame `push rs; body; pop r k` (cdecl code passes a callee's arguments in
one) runs its body from `pushed rs s`, and the pop leads to `popped r k s₂`
(`WP.frame`), provided the body leaves `esp` where the push put it.

For constant time, `RelCT.call` relates two runs of a call of verified code
through the callee's `ConstantTime` proof, and `RelCT.frame` two runs of a
frame whose body is related: the addresses the call, return, push and pop
instructions access depend only on `esp`.
-/

namespace VG.X86

/-! ## Calls -/

/-- The state a called function starts in: `esp` moved down by 4 and the
return address (the next of the state's unknowns) stored there. -/
def State.callEntry (s : State) : State :=
  { s.setReg .esp (s.gpr .esp - 4) with
    mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0)
    unknowns := fun n => s.unknowns (n + 1) }

theorem call_callEntry (s : State) : isa.call s = some s.callEntry := rfl

@[simp] theorem State.callEntry_rd (s : State) : s.callEntry.rd = s.rd := rfl
@[simp] theorem State.callEntry_wr (s : State) : s.callEntry.wr = s.wr := rfl
@[simp] theorem State.callEntry_esp (s : State) : s.callEntry.gpr .esp = s.gpr .esp - 4 := by
  simp [State.callEntry, State.setReg]
theorem State.callEntry_gpr (s : State) {r : Reg} (h : r ≠ .esp) : s.callEntry.gpr r = s.gpr r := by
  simp [State.callEntry, State.setReg, h]
theorem State.callEntry_mem (s : State) :
    s.callEntry.mem = s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0) := rfl

/-- Calling verified code without calls or frames: from a state `s` such
that, once the call has stored its return address (`State.callEntry`), the
callee's precondition holds with its permissions narrowed to `rd` and `wr`,
the call returns in a state that has the permissions of `s`, its
callee-saved registers and `esp`; whose memory differs from that of
`s.callEntry` only within `wr`; and whose memory and registers (`esp` aside)
are those of a state satisfying the callee's postcondition. -/
theorem WP.call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame wr s.callEntry.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .esp → s₂.gpr r = s'.gpr r) ∧
        k.post (s.callEntry.withRegions rd wr) s₂) → Q s')
    (hn : c.noCalls = true := by decide +kernel) : WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr, hf⟩ := Exec.regions he hn
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions] at he'
  rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at he'
  set s₂ := s₁.withRegions s.rd s.wr with hs₂
  have hsp₂ : s₂.gpr .esp = s.gpr .esp - 4 := by
    rw [hs₂, State.withRegions_gpr, habi.1 .esp (by simp [calleeSaved])]; simp
  have hret : isa.ret s.callEntry s₂ = some (s₂.setReg .esp (s₂.gpr .esp + 4)) := by
    simp only [isa, ret]
    refine ite_eq_left ⟨by rw [hsp₂, State.callEntry_esp], ?_⟩
    have := habi.2
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_esp] at this
    rw [hsp₂, State.callEntry_esp]; exact this
  have hesp : (s₂.setReg .esp (s₂.gpr .esp + 4)).gpr .esp = s.gpr .esp := by
    simp only [State.setReg, ite_true, hsp₂]; exact BitVec.sub_add_cancel _ _
  have hkeep : ∀ r, r ≠ .esp → (s₂.setReg .esp (s₂.gpr .esp + 4)).gpr r = s₂.gpr r :=
    fun r h => by simp [State.setReg, h]
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl (fun r hr' => ?_) hf
    ⟨s₁, rfl, fun r h => (hkeep r h).symm, hpost⟩⟩
  by_cases h : r = .esp
  · subst h; exact hesp
  · rw [hkeep r h, hs₂, State.withRegions_gpr, habi.1 r hr', State.withRegions_gpr,
      State.callEntry_gpr _ h]

/-! ## Frames -/

/-- The state a frame's body starts in, after `push rs`: the registers
stored below `esp`, and those bytes a writable region, at the head of `wr`. -/
def pushed (rs : List Reg) (s : State) : State :=
  { pushRegs s rs with
    wr := ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * rs.length)).setWidth 64, 4 * rs.length⟩ :: s.wr }

/-- The state after the pop of a frame, `pop r k`, from the state `s` its
body ends in. -/
def popped (r : Reg) (k : Nat) (s : State) : State := { popReg s r k with wr := s.wr.tail }

theorem push_pushed {rs : List Reg} {s : State} (h₁ : rs ≠ []) (h₂ : Reg.esp ∉ rs)
    (h₃ : 4 * rs.length ≤ (s.gpr .esp).toNat) : isa.push (.push rs) s = some (pushed rs s) := by
  simp only [isa, push, ne_eq, h₁, not_false_eq_true, h₂, h₃, and_self, ite_true]
  rfl

theorem pushed_esp (rs : List Reg) (s : State) :
    (pushed rs s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) :=
  (pushRegs_eq s rs).2.2.1

theorem pushed_gpr (rs : List Reg) (s : State) {r : Reg} (h : r ≠ .esp) :
    (pushed rs s).gpr r = s.gpr r :=
  (pushRegs_eq s rs).2.2.2 r h

@[simp] theorem pushed_rd (rs : List Reg) (s : State) : (pushed rs s).rd = s.rd :=
  (pushRegs_eq s rs).1

@[simp] theorem pushed_wr (rs : List Reg) (s : State) :
    (pushed rs s).wr =
      ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * rs.length)).setWidth 64, 4 * rs.length⟩ :: s.wr := rfl

theorem popped_esp (r : Reg) (k : Nat) (s : State) :
    (popped r k s).gpr .esp = s.gpr .esp + BitVec.ofNat 32 (4 * k) :=
  (popReg_eq s r k).2.2.1

theorem popped_gpr (r : Reg) (k : Nat) (s : State) {q : Reg} (h₁ : q ≠ .esp) (h₂ : q ≠ r) :
    (popped r k s).gpr q = s.gpr q :=
  (popReg_eq s r k).2.2.2 q h₁ h₂

@[simp] theorem popped_rd (r : Reg) (k : Nat) (s : State) : (popped r k s).rd = s.rd :=
  (popReg_eq s r k).1

@[simp] theorem popped_wr (r : Reg) (k : Nat) (s : State) : (popped r k s).wr = s.wr.tail := rfl

theorem popReg_mem (s : State) (r : Reg) (k : Nat) : (popReg s r k).mem = s.mem := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

@[simp] theorem popped_mem (r : Reg) (k : Nat) (s : State) : (popped r k s).mem = s.mem :=
  popReg_mem s r k

/-- A frame: its body runs from `pushed rs s`, and if it ends with `esp`
where the push left it, the pop leads to `popped r k s₂`. -/
theorem WP.frame {rs : List Reg} {r : Reg} {k : Nat} {body : Prog isa} {s : State}
    {Q : State → Prop} (h₁ : rs ≠ []) (h₂ : Reg.esp ∉ rs)
    (h₃ : 4 * rs.length ≤ (s.gpr .esp).toNat) (hk : k = rs.length) (hr : r ≠ .esp)
    (hb : WP isa body (pushed rs s) fun s₂ =>
      s₂.gpr .esp = (pushed rs s).gpr .esp ∧ Q (popped r k s₂)) :
    WP isa (.frame (.push rs) body (.pop r k)) s Q := by
  obtain ⟨t, s₂, he, hsp, hq⟩ := hb
  obtain ⟨-, hw⟩ := Exec.rdwr he
  have hk0 : k ≠ 0 := by subst hk; exact fun h => h₁ (List.length_eq_zero_iff.mp h)
  have hpop : isa.pop (.pop r k) (pushed rs s) s₂ = some (popped r k s₂) := by
    simp only [isa, pop]
    refine ite_eq_left ⟨hk0, hr, hsp, hw, ?_⟩
    rw [pushed_wr, pushed_esp, hk]; rfl
  exact ⟨_, _, Exec.frame (push_pushed h₁ h₂ h₃) he hpop, hq⟩

/-! ## Constant time -/

/-- The trace of a run of verified code without calls, with more
permissions than its contract gives it, is that of the run its contract
describes. -/
theorem trace_narrow {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {t : List Leak} {s' : State}
    (he : Exec isa c s t s') :
    ∃ s'', Exec isa c (s.withRegions rd wr) t s'' := by
  obtain ⟨t', s'', he', -⟩ := hv _ hpre
  have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, -⟩ := Exec.det he hw'
  exact ⟨_, he'⟩

/-- Two runs of a call of verified code leak the same trace when the
callee's contract holds in both (narrowed to the regions it is given, as
`WP.call` does), its public data agrees, and so does `esp`. -/
theorem RelCT.call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ Covers wr s₁.wr ∧
      Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ Covers wr s₂.wr ∧ s₁.gpr .esp = s₂.gpr .esp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨p₁, p₂, hpub, c₁, w₁, c₂, w₂, hsp⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨_, n₁⟩ := trace_narrow hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨_, n₂⟩ := trace_narrow hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      have ht := hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂
      have q₁ := (ret_gpr r₁ .esp).1
      have q₂ := (ret_gpr r₂ .esp).1
      simp only [State.callEntry_esp] at q₁ q₂
      refine ⟨?_, trivial⟩
      simp only [q₁, q₂, hsp, ht]

/-- Two runs of a frame leak the same trace when `esp` agrees and the runs of
its body, from the states after the push, do. -/
theorem RelCT.frame {rs : List Reg} {r : Reg} {k : Nat} {body : Prog isa}
    {P R : State → State → Prop} (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .esp = s₂.gpr .esp)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed rs s₁ ∧ b = pushed rs s₂) body R) :
    RelCT isa P (.frame (.push rs) body (.pop r k)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hpush : ∀ {s a : State}, isa.push (.push rs) s = some a → a = pushed rs s := by
    intro s a h
    simp only [isa, push] at h
    split at h <;> cases h; rfl
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea := hpush p₁
      have eb := hpush p₂
      subst ea eb
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      have g₁ := (pop_eq q₁).2.2.2.2.1
      have g₂ := (pop_eq q₂).2.2.2.2.1
      rw [pushed_esp] at g₁ g₂
      have e := hsp _ _ hp
      refine ⟨?_, trivial⟩
      simp only [addrs, g₁, g₂, e]

end VG.X86

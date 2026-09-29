import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# Constant time of calls, by relating two runs (x86, 32-bit)

Untrusted: everything here is checked by Lean.

The taint analysis follows calls and frames, but forgets what a callee
stores through pointers it cannot place in a region (such as a pointer into
the middle of one), and with it the public values its caller keeps in memory.
Code that calls such functions can be related piece by piece instead
(`RelCT`), as on the other targets (`Proof/Framework/X86_64/RelCT.lean`).

A call of verified code leaks the same trace in two runs when the callee's
contract holds in both (narrowed to the regions it is given, as `WP.call`
does) and its public data agrees (`RelCT.call`): the callee's run from the
narrowed state is the actual run with fewer permissions (`Exec.widen` and
determinism), and the callee is constant time. The addresses the call and
return instructions, and a frame's push and pop (`RelCT.frame`), access
depend only on `esp`. `RelCT.callWith` combines them for a call in a frame
of its arguments (`WP.callWith`).

`τr rs` is the taint state in which only the registers `rs` are public, for
the pieces the taint analysis proves (`RelCT.taint`).
-/

namespace VG.X86

/-- The trace of a run of verified code, with more permissions than its
contract gives it, is that of the run its contract describes. -/
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
callee's contract holds in both (narrowed to the regions it is given), its
public data agrees, and so does `esp`. -/
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
    obtain ⟨_, e, -, -, -, rfl⟩ := push_some h
    cases e; rfl
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

/-- Two runs of a call in a frame of its arguments leak the same trace when
the callee's contract holds in both, its public data agrees, and so does
`esp`. -/
theorem RelCT.callWith {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ → CallPre k rs rd wr s₁ ∧ CallPre k rs rd wr s₂ ∧
      s₁.gpr .esp = s₂.gpr .esp ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr)) :
    RelCT isa P (.frame (.push rs) (.call n c) (.pop .eax rs.length)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP _ _ h).2.2.1) (RelCT.call hv hct rd wr ?_)
  rintro _ _ ⟨s₁, s₂, h, rfl, rfl⟩
  obtain ⟨k₁, k₂, hsp, hpub⟩ := hP _ _ h
  refine ⟨k₁.pre, k₂.pre, hpub, by rw [pushed_rd, pushed_wr]; exact k₁.cov, by rw [pushed_wr]; exact k₁.covw,
    by rw [pushed_rd, pushed_wr]; exact k₂.cov, by rw [pushed_wr]; exact k₂.covw, ?_⟩
  rw [pushed_esp, pushed_esp, hsp]

/-! ## Pieces the taint analysis proves -/

/-- A taint state in which only the registers `rs` are public. -/
def τr (rs : List Reg) : Taint.T := { regs := .ofList rs, flags := false }

theorem agree_regs {rs : List Reg} {x y : State} (h : ∀ r ∈ rs, x.gpr r = y.gpr r) :
    Taint.Agree (τr rs) x y := by
  have wf : ∀ s : State, Taint.Wf (τr rs) s := fun s =>
    Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0),
      fun _ h => (List.not_mem_nil h).elim⟩
  exact ⟨⟨fun r hr => h r (by simpa [τr, RegSet.mem_ofList] using hr), fun h => nomatch h⟩,
    fun h => absurd rfl h, wf x, wf y, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- An empty block. -/
theorem RelCT.nil {P Q : State → State → Prop} (h : ∀ x y, P x y → Q x y) :
    RelCT isa P (.block []) Q := by
  intro x y t₁ t₂ x' y' hp e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, h _ _ hp⟩

end VG.X86

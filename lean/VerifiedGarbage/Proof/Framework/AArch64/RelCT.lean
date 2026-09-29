import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# Constant time of calls, by relating two runs (AArch64)

Untrusted: everything here is checked by Lean.

As on x86-64 (`Proof/Framework/X86_64/RelCT.lean`): a call of verified code
leaks the same trace in two runs when the callee's contract holds in both
(narrowed to the regions it is given, as `WP.call` does) and its public data
agrees, since the callee's run from the narrowed state is the actual run
with fewer permissions (`Exec.widen` and determinism), and the callee is
constant time. `bl` and `ret` leak no addresses of their own.

A frame saving a register (`RelCT.frameReg`) leaks the address of its slot,
twice, around what its body leaks, so it is constant time when the stack
pointers agree and the body is, run as `WP.frameReg` runs it (in the
permissions of the frame's caller).
-/

namespace VG.AArch64

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

theorem RelCT.call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ Covers wr s₁.wr ∧
      Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ Covers wr s₂.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨_, n₁⟩ := trace_narrow hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨_, n₂⟩ := trace_narrow hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      have ht := hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂
      exact ⟨by simp only [ht], trivial⟩

/-- A call of verified code, narrowed in each run to regions of its own. -/
theorem RelCT.callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨_, n₁⟩ := trace_narrow hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨_, n₂⟩ := trace_narrow hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      have ht := hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂
      exact ⟨by simp only [ht], trivial⟩

/-- The state the body of a frame saving `r` runs in, as `WP.frameReg` runs
it: the push done, in the permissions of the frame's caller. -/
abbrev frameInner (r : Reg) (s : State) : State :=
  { s with sp := s.sp - 16, mem := s.mem.write (s.sp - 16) 8 (s.gpr r) }

/-- A run of a frame's body from `pushed r s` is its run from
`frameInner r s`, with the frame's permission. -/
theorem trace_frame {r : Reg} {main : Prog isa} {s : State} {t t' : List Leak} {s₂ s' : State}
    (he : Exec isa main (pushed r s) t s₂) (hi : Exec isa main (frameInner r s) t' s') : t = t' := by
  have hw := Exec.widen hi (rd := s.rd) (wr := ⟨s.sp - 16, 16⟩ :: s.wr)
    (fun a n h => InRegions_append_cons.mpr (.inr h))
    (fun a n h => InRegions_append_cons (xs := []).mpr (.inr h))
  exact (Exec.det he hw).1

theorem push_pushed_eq {r : Reg} {s s₁ : State} (h : isa.push (.push r) s = some s₁) : s₁ = pushed r s := by
  have hs : 16 ≤ s.sp.toNat := by
    by_contra hc
    have : isa.push (.push r) s = none := by
      show push (.push r) s = none
      unfold push
      simp [hc]
    rw [this] at h; cases h
  rw [push_pushed hs, Option.some.injEq] at h
  exact h.symm

/-- A frame saving `r`: constant time when the stack pointers agree, the
body is constant time from `frameInner`, and the body terminates there. -/
theorem RelCT.frameReg {r : Reg} {main : Prog isa} {P : State → State → Prop}
    (hm : RelCT isa (fun s₁ s₂ => ∃ a b, P a b ∧ s₁ = frameInner r a ∧ s₂ = frameInner r b) main
      fun _ _ => True)
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ (∃ t s', Exec isa main (frameInner r s₁) t s') ∧
      ∃ t s', Exec isa main (frameInner r s₂) t s') :
    RelCT isa P (.frame (.push r) main (.pop r)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨hsp, ⟨u₁, v₁, x₁⟩, ⟨u₂, v₂, x₂⟩⟩ := hP _ _ hp
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := push_pushed_eq p₁
      obtain rfl := push_pushed_eq p₂
      have h₁ := trace_frame b₁ x₁
      have h₂ := trace_frame b₂ x₂
      have ht := (hm _ _ _ _ _ _ ⟨_, _, hp, rfl, rfl⟩ x₁ x₂).1
      have sp₁ := (Exec.rdwr b₁).2.2
      have sp₂ := (Exec.rdwr b₂).2.2
      refine ⟨?_, trivial⟩
      show (addrs (.push r) s₁).map Leak.addr ++ _ ++ (addrs (.pop r) _).map Leak.addr =
        (addrs (.push r) s₂).map Leak.addr ++ _ ++ (addrs (.pop r) _).map Leak.addr
      simp only [addrs, sp₁, sp₂, pushed, hsp, h₁, h₂, ht]

end VG.AArch64

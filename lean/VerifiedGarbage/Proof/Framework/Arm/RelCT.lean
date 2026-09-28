import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Call

/-!
# Calls of code that makes calls, and constant time by relating two runs (ARMv7)

Untrusted: everything here is checked by Lean.

`WP.callCalls` is `WP.call` for a callee that makes calls of its own (but
has no frames): the registers it keeps are those none of its instructions
writes, other than those a call changes (`linkRegs`).

`RelCT.call`, as on AArch64 (`Proof/Framework/AArch64/RelCT.lean`): a call of
verified code leaks the same trace in two runs when the callee's contract
holds in both (narrowed to the regions it is given, as `WP.call` does) and
its public data agrees, since the callee's run from the narrowed state is
the actual run with fewer permissions (`Exec.widen` and determinism), and
the callee is constant time. `bl` and `bx lr` leak no addresses of their
own.
-/

namespace VG.Arm

/-- `WP.call` for a callee that makes calls but has no frames. -/
theorem WP.callCalls {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      (∀ r, (∀ i ∈ instrs c, dstOf i ≠ some r) → r ∉ linkRegs → s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hn : c.noFrames = true := by decide +kernel) : WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr, -, hf⟩ := Exec.regions he hn
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions] at he'
  rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at he'
  have hret : isa.ret s.callEntry (s₁.withRegions s.rd s.wr) = some (s₁.withRegions s.rd s.wr) := by
    have h := habi.1 .lr (by decide)
    simp only [State.withRegions_gpr] at h
    simp only [isa, ret, State.withRegions_gpr, h, ite_true]
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl habi.2 hf (fun r hr' hlr => ?_)
    (fun r hr' hl => ?_) ?_⟩
  · simp only [State.withRegions_gpr]
    rw [habi.1 r hr', State.withRegions_gpr, State.callEntry_gpr s (preserved_not_link r hr' hlr)]
  · rw [Exec.gpr hr' he' (.inr hl), State.callEntry_gpr s hl]
  · have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
      rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
    rw [this]; exact hpost

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

end VG.Arm

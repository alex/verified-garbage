import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# Constant time of calls, by relating two runs (x86-64)

Untrusted: everything here is checked by Lean.

A call of verified code leaks the same trace in two runs when the callee's
contract holds in both (narrowed to the regions it is given, as `WP.call`
does) and its public data agrees: the callee's run from the narrowed state
is the actual run with fewer permissions (`Exec.widen` and determinism),
and the callee is constant time. The call and return addresses agree when
`rsp` does.
-/

namespace VG.X86_64

theorem ret_rsp {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s₂.gpr .rsp = s₁.gpr .rsp := by
  simp only [isa, ret] at h
  split at h
  · exact ‹_ ∧ _›.1
  · cases h

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
  simp only [State.withRegions_withRegions] at hw'
  rw [show s.withRegions s.rd s.wr = s from rfl] at hw'
  obtain ⟨rfl, -⟩ := Exec.det he hw'
  exact ⟨_, he'⟩

theorem RelCT.call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ Covers wr s₁.wr ∧
      Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ Covers wr s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
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
      have q₁ := ret_rsp r₁
      have q₂ := ret_rsp r₂
      simp only [State.callEntry_rsp] at q₁ q₂
      refine ⟨?_, trivial⟩
      simp only [q₁, q₂, hsp, ht]

end VG.X86_64

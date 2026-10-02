import VerifiedGarbage.Proof.Argon2.AArch64.DeriveFrame
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Saving and restoring the private frame leaks only the public stack pointer. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem push_some {s t : State} {r : Reg} (h : isa.push (.push r) s = some t) : t = pushed r s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem alloc_some {s t : State} (h : isa.push (.alloc 272) s = some t) : t = allocated 272 s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem push_rel {r : Reg} {body : Prog isa} {P : State → State → Prop}
    (sp : ∀ s t, P s t → s.sp = t.sp)
    (run : RelCT isa (fun a b => ∃ s t, P s t ∧ a = pushed r s ∧ b = pushed r t)
      body (fun _ _ => True)) :
    RelCT isa P (.frame (.push r) body (.pop r)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u v hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      cases push_some p₁
      cases push_some p₂
      obtain ⟨eq, _⟩ := run _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      simp only [addrs, Exec.sp b₁, Exec.sp b₂, pushed, sp _ _ hp, eq]

theorem alloc_rel {body : Prog isa} {P : State → State → Prop}
    (run : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated 272 s ∧ b = allocated 272 t)
      body (fun _ _ => True)) :
    RelCT isa P (.frame (.alloc 272) body (.free 272)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u v hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      cases alloc_some p₁
      cases alloc_some p₂
      obtain ⟨eq, _⟩ := run _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨by simpa only [addrs, List.map_nil, List.nil_append, List.append_nil] using eq, trivial⟩

theorem frame_rel (rs : List Reg) (body : Prog isa) (P : State → State → Prop)
    (sp : ∀ s t, P s t → s.sp = t.sp)
    (run : RelCT isa (fun a b => ∃ s t, P s t ∧ a = frameStart s rs ∧ b = frameStart t rs)
      body (fun _ _ => True)) :
    RelCT isa P (Impl.Argon2.AArch64.Derive.frame body rs) (fun _ _ => True) := by
  induction rs generalizing P with
  | nil => exact alloc_rel run
  | cons r rs ih =>
    apply push_rel sp
    apply ih (fun a b => ∃ s t, P s t ∧ a = pushed r s ∧ b = pushed r t) ?_ ?_
    · rintro a b ⟨s, t, hp, rfl, rfl⟩
      change s.sp - 16 = t.sp - 16
      rw [sp s t hp]
    · apply run.mono ?_ (fun _ _ h => h)
      rintro a b ⟨u, v, ⟨s, t, hp, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨s, t, hp, rfl, rfl⟩
end VG.Proof.Argon2.AArch64.Derive

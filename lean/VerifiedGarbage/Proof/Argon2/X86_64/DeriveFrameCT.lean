import VerifiedGarbage.Proof.Argon2.X86_64.DeriveFrame

/-! Saving and restoring the ABI frame leaks only the public stack pointer. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frame_rel (rs : List Reg) (body : Prog isa) (P : State → State → Prop)
    (sp : ∀ s t, P s t → s.gpr .rsp = t.gpr .rsp)
    (run : RelCT isa (fun a b => ∃ s t, P s t ∧ a = frameStart s rs ∧ b = frameStart t rs)
      body (fun _ _ => True)) :
    RelCT isa P (Impl.Argon2.X86_64.Derive.frame body rs) (fun _ _ => True) := by
  induction rs generalizing P with
  | nil => exact RelCT.frame sp run
  | cons r rs ih =>
    apply RelCT.frame sp
    apply ih (fun a b => ∃ s t, P s t ∧ a = pushed [r] s ∧ b = pushed [r] t) ?_ ?_
    · rintro a b ⟨s, t, hp, rfl, rfl⟩
      rw [pushed_rsp, pushed_rsp, sp s t hp]
    · apply run.mono ?_ (fun _ _ h => h)
      rintro a b ⟨u, v, ⟨s, t, hp, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨s, t, hp, rfl, rfl⟩

end VG.Proof.Argon2.X86_64.Derive

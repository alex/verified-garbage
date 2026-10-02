import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Running code from a narrowed state

Untrusted: everything here is checked by Lean.

Code proven from a state `n s` that permits less memory than `s` (its
regions narrowed) runs from `s` with the same trace, ending in the state it
ends in from `n s` with the regions of `s` (each ISA's `Exec.widen`). The
lemmas here take that as a hypothesis (`hw`), so that one statement serves
every ISA: `WP.of_narrow` moves a correctness proof from `n s` to `s`, and
`RelCT.of_narrow` a proof of constant time between two runs, by
determinism.
-/

namespace VG

variable {M : ISA}

/-- A correctness proof from the narrowed state `n`, from `s`: the final
state is the one from `n`, widened (`w`). -/
theorem WP.of_narrow {c : Prog M} {s n : M.State} {Q : M.State → Prop} (w : M.State → M.State)
    (hw : ∀ t s₁, Exec M c n t s₁ → Exec M c s t (w s₁)) (h : WP M c n Q) :
    WP M c s fun s' => ∃ s₁, s' = w s₁ ∧ Q s₁ := by
  obtain ⟨t, s₁, he, hq⟩ := h
  exact ⟨t, w s₁, hw t s₁ he, s₁, rfl, hq⟩

/-- Constant time from narrowed states (`n`): two runs from states related
by `P`, each satisfying `G`, leak what the runs from their narrowed states
leak, which `h` relates, as long as both of those terminate (`hex`). -/
theorem RelCT.of_narrow {c : Prog M} {P : M.State → M.State → Prop} (G : M.State → Prop)
    (n : M.State → M.State) (w : M.State → M.State → M.State)
    (hG : ∀ s₁ s₂, P s₁ s₂ → G s₁ ∧ G s₂)
    (hw : ∀ s, G s → ∀ t s₁, Exec M c (n s) t s₁ → Exec M c s t (w s s₁))
    (hex : ∀ s, G s → ∃ t s', Exec M c (n s) t s')
    (h : RelCT M (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = n s₁ ∧ b = n s₂) c fun _ _ => True) :
    RelCT M P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨g₁, g₂⟩ := hG _ _ hp
  obtain ⟨u₁, r₁, f₁⟩ := hex _ g₁
  obtain ⟨u₂, r₂, f₂⟩ := hex _ g₂
  rw [(Exec.det e₁ (hw _ g₁ _ _ f₁)).1, (Exec.det e₂ (hw _ g₂ _ _ f₂)).1]
  exact ⟨(h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ f₁ f₂).1, trivial⟩

end VG

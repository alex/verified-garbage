import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Block

/-!
# Regrouping sequences in relational constant-time proofs

Untrusted: everything here is checked by Lean.

Structured code nests its sequences to the right, `a; (b; c)`, but a
relational proof (`RelCT`) often wants to split it elsewhere, e.g. to check
everything before a call with the taint analysis at once (`RelCT.taint`) and
relate the call by its callee's contract (`RelCT.callWith`): `RelCT.assoc`
regroups `a; (b; c)` as `(a; b); c`, which runs the same and leaks the same
trace; `WP.assoc` does the same for the correctness proofs, and `WP.ite_true`
and `WP.ite_false` take the branch a relational proof is in.
-/

namespace VG

variable {M : ISA}

theorem RelCT.assoc {P Q : M.State → M.State → Prop} {a b c : Prog M}
    (h : RelCT M P (.seq (.seq a b) c) Q) : RelCT M P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ e₁ =>
    cases e₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq a₂ e₂ =>
        cases e₂ with
        | seq b₂ c₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ b₁) c₁) (.seq (.seq a₂ b₂) c₂)
          simp only [List.append_assoc] at ht
          exact ⟨ht, hq⟩

/-- An empty block. -/
theorem RelCT.block_nil {P Q : M.State → M.State → Prop} (h : ∀ x y, P x y → Q x y) :
    RelCT M P (.block []) Q := by
  intro x y t₁ t₂ x' y' hp e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, h _ _ hp⟩

theorem WP.assoc {a b c : Prog M} {s : M.State} {Q : M.State → Prop}
    (h : WP M (.seq (.seq a b) c) s Q) : WP M (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem WP.assoc' {a b c : Prog M} {s : M.State} {Q : M.State → Prop}
    (h : WP M (.seq a (.seq b c)) s Q) : WP M (.seq (.seq a b) c) s Q :=
  WP.seq (WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq_iff.mp h))

theorem WP.ite_true {c : M.Cond} {th el : Prog M} {s : M.State} {Q : M.State → Prop}
    (h : WP M (.ite c th el) s Q) (hc : M.eval c s = some true) : WP M th s Q := by
  obtain ⟨t, s', e, hq⟩ := h
  cases e with
  | iteT _ e => exact ⟨_, _, e, hq⟩
  | iteF hc' _ => rw [hc] at hc'; cases hc'

theorem WP.ite_false {c : M.Cond} {th el : Prog M} {s : M.State} {Q : M.State → Prop}
    (h : WP M (.ite c th el) s Q) (hc : M.eval c s = some false) : WP M el s Q := by
  obtain ⟨t, s', e, hq⟩ := h
  cases e with
  | iteT hc' _ => rw [hc] at hc'; cases hc'
  | iteF _ e => exact ⟨_, _, e, hq⟩

end VG

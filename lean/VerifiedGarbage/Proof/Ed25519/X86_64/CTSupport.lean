import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.Field

/-! Retain separate functional postconditions for two secret inputs. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64

set_option hygiene false in
/-- `taint_decide` for the code emitted with `fld`, for each field arithmetic it may be. -/
macro "fld_taint_decide" : tactic =>
  `(tactic| first
    | (rcases (EdArith.known (fld := fld)) with h | h <;> (rw [h]; exact ⟨_, by taint_decide⟩))
    | exact ⟨_, by taint_decide⟩)

set_option hygiene false in
/-- `lit_decide` for the code emitted with `fld`, for each field arithmetic it may be. -/
macro "fld_lit_decide" : tactic =>
  `(tactic| first
    | (rcases (EdArith.known (fld := fld)) with h | h <;> (rw [h]; lit_decide))
    | lit_decide)

/-- `RelCT.taint`, with the hint found by `fld_taint_decide` for each field arithmetic. -/
theorem taintFld {P : State → State → Prop} {c : Prog isa} (τ : VG.X86_64.Taint.T)
    (hp : ∀ s₁ s₂, P s₁ s₂ → VG.X86_64.Taint.Agree τ s₁ s₂)
    (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T, (VG.X86_64.taint.check τ c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  let ⟨_, h⟩ := h; VG.RelCT.taint (A := VG.X86_64.taint) τ hp h

/-- `RelCT.taintRegs`, with the hint found by `fld_taint_decide`. -/
theorem taintRegsFld {τ : VG.X86_64.Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s₁ s₂, P s₁ s₂ → VG.X86_64.Taint.Agree τ s₁ s₂) (rs : List Reg)
    (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T,
      ((VG.X86_64.taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ'.regs) = some true) :
    RelCT isa P c fun s₁ s₂ => ∀ r ∈ rs, s₁.gpr r = s₂.gpr r :=
  let ⟨_, h⟩ := h; VG.X86_64.RelCT.taintRegs hp rs h

theorem execBlock_append_seq {xs ys : List Instr} {s t : State} {tr : List Leak}
    (h : Exec isa (.block (xs ++ ys)) s tr t) :
    Exec isa (.seq (.block xs) (.block ys)) s tr t := by
  rw [Exec.block_iff, execBlock_append] at h
  obtain ⟨⟨u, tx⟩, hu, ht⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨v, ty⟩, hv, he⟩ := Option.map_eq_some_iff.mp ht
  cases he
  exact .seq (.block hu) (.block hv)

theorem blockAppend_ct {P R Q : State → State → Prop} {xs ys : List Instr}
    (hx : RelCT isa P (.block xs) R) (hy : RelCT isa R (.block ys) Q) :
    RelCT isa P (.block (xs ++ ys)) Q :=
  fun _ _ _ _ _ _ hp ex ey => VG.RelCT.seq hx hy _ _ _ _ _ _ hp
    (execBlock_append_seq ex) (execBlock_append_seq ey)

theorem withRuns {P Q F₁ F₂ : State → State → Prop} {c : Prog isa}
    (h : RelCT isa P c Q)
    (hw : ∀ x y, P x y → WP isa c x (F₁ x) ∧ WP isa c y (F₂ y)) :
    RelCT isa P c fun x' y' => Q x' y' ∧ ∃ x y, P x y ∧ F₁ x x' ∧ F₂ y y' := by
  intro x y tx ty x' y' hp ex ey
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp ex ey
  obtain ⟨⟨_, u, eu, hu⟩, ⟨_, v, ev, hv⟩⟩ := hw x y hp
  obtain ⟨-, rfl⟩ := Exec.det ex eu
  obtain ⟨-, rfl⟩ := Exec.det ey ev
  exact ⟨ht, hq, x, y, hp, hu, hv⟩

end VG.Proof.Ed25519.X86_64

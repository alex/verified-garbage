import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# ML-KEM on x86-64: constant time by relating two runs

The functions that call `vg_mlkem_sample_ntt`, or run its loop, are proven
constant time piece by piece (`RelCT`, see `Proof/Framework/RelCT.lean`): two
runs from entry states `σ₁`, `σ₂` that satisfy the precondition and agree on
the public data are related, between the pieces, by the invariant `I` of the
correctness proof holding of each (`Rel2`). Each piece leaks the same in both
runs (by the taint analysis from registers that `I` says hold the same public
values, `taintRel`, or by a callee's proof, `RelCT.callEx`), and correctness
gives the next invariant (`relInv`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- Two states each related by `I` to an entry state; the entry states
satisfy `Pre` and agree by `Pub`. -/
def Rel2 (Pre : State → Prop) (Pub : State → State → Prop) (I : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ I σ₁ s₁ ∧ I σ₂ s₂

/-- A piece that leaks the same from states related by `I`, and takes each
run from `I` to `I'`. -/
theorem relInv {Pre : State → Prop} {Pub : State → State → Prop} {I I' : State → State → Prop}
    {c : Prog isa} (hw : ∀ σ s, Pre σ → I σ s → WP isa c s (I' σ))
    (ht : RelCT isa (Rel2 Pre Pub I) c fun _ _ => True) :
    RelCT isa (Rel2 Pre Pub I) c (Rel2 Pre Pub I') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩

/-- Constant time, from a relation of the runs from the entry states. -/
theorem relStart {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Rel2 Pre Pub fun σ s => s = σ) c Q) : ConstantTime isa Pre Pub c :=
  RelCT.constantTime (RelCT.mono h (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => ⟨s₁, s₂, p₁, p₂, hp, rfl, rfl⟩) fun _ _ h => h)

/-- Code the taint analysis proves constant time from the registers `rs`,
which hold the same values in runs related by `P`. -/
theorem taintRel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (X86_64.Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (X86_64.Taint.ofRegs rs) (fun x y hp => X86_64.Taint.agree_ofRegs (hr x y hp)) h

/-- The final states of two runs related by `P` satisfy what correctness
says of each, from its own initial state. -/
theorem RelCT.postDep {P Q : State → State → Prop} {c : Prog isa} {F : State → State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (F y))
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → Q x' y') : RelCT isa P c Q :=
  RelCT.mono (RelCT.wpDep h hw) (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, f₁, f₂⟩ => hQ _ _ _ _ hp f₁ f₂

end VG.Proof.MlKem.X86_64

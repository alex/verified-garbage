import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
import VerifiedGarbage.Proof.MlKem.AArch64.MemTaint

/-!
# ML-DSA on AArch64: constant time of the sampling functions, piece by piece

Untrusted: everything here is checked by Lean. Two runs of a sampling
function, from entry states `σ₁` and `σ₂` that satisfy the precondition and
agree on what is public, are related at each point by what correctness
proves of each (`Rel2 Pre Pub J`: `J σᵢ sᵢ`). A piece of code leaks the same
in both runs, and takes them from `J` to `J'`, if the taint analysis proves
it constant time from registers that `J` makes equal (`relTaint`), or if it
only touches memory on which both runs agree, where `memTaint` does
(`relMem`); by determinism, the runs then end in states that correctness
describes (`relStep`).
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64

/-- Two runs, from entry states `σ₁` and `σ₂` related by `Pre` and `Pub`,
in the states that `J` describes. -/
def Rel2 (Pre : State → Prop) (Pub : State → State → Prop) (J : State → State → Prop)
    (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ J σ₁ s₁ ∧ J σ₂ s₂

section
variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- A piece that leaks the same from runs related by `J`, and takes each
run from `J` to `J'`. -/
theorem relStep {J J' : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, Pre σ → J σ s → WP isa c s (J' σ))
    (ht : RelCT isa (Rel2 Pre Pub J) c fun _ _ => True) :
    RelCT isa (Rel2 Pre Pub J) c (Rel2 Pre Pub J') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ := h
  refine ⟨(ht _ _ _ _ _ _ ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ e₁ e₂).1, σ₁, σ₂, p₁, p₂, hq, ?_, ?_⟩
  · obtain ⟨_, _, f, g⟩ := hw σ₁ s₁ p₁ j₁
    obtain ⟨-, rfl⟩ := Exec.det e₁ f
    exact g
  · obtain ⟨_, _, f, g⟩ := hw σ₂ s₂ p₂ j₂
    obtain ⟨-, rfl⟩ := Exec.det e₂ f
    exact g

/-- Code the taint analysis proves constant time from the registers `rs`,
which agree in runs related by `J`. -/
theorem relTaint {J : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ σ₁ σ₂ s₁ s₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → J σ₁ s₁ → J σ₂ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Rel2 Pre Pub J) c fun _ _ => True :=
  RelCT.taint (A := taint) _ (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ =>
    let ⟨hsp, hrs⟩ := hr σ₁ σ₂ s₁ s₂ p₁ p₂ hq j₁ j₂
    Proof.MlKem.AArch64.agree_of hsp hrs) h

theorem vectorRelTaint {J : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ σ₁ σ₂ s₁ s₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → J σ₁ s₁ → J σ₂ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VectorTaint.T} (h : (VectorTaint.taint.check (VectorTaint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Rel2 Pre Pub J) c fun _ _ => True :=
  VectorTaint.relCT _ (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ =>
    let ⟨hsp, hrs⟩ := hr σ₁ σ₂ s₁ s₂ p₁ p₂ hq j₁ j₂
    Proof.MlKem.AArch64.agree_of hsp hrs) h

/-- `relStep` of `relTaint`. -/
theorem relTaintStep {J J' : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hw : ∀ σ s, Pre σ → J σ s → WP isa c s (J' σ))
    (hr : ∀ σ₁ σ₂ s₁ s₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → J σ₁ s₁ → J σ₂ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Rel2 Pre Pub J) c (Rel2 Pre Pub J') :=
  relStep hw (relTaint rs hr h)

theorem vectorRelTaintStep {J J' : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hw : ∀ σ s, Pre σ → J σ s → WP isa c s (J' σ))
    (hr : ∀ σ₁ σ₂ s₁ s₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → J σ₁ s₁ → J σ₂ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VectorTaint.T} (h : (VectorTaint.taint.check (VectorTaint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Rel2 Pre Pub J) c (Rel2 Pre Pub J') :=
  relStep hw (VectorTaint.relRegs rs (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ =>
    hr σ₁ σ₂ s₁ s₂ p₁ p₂ hq j₁ j₂) h)

/-- Code that runs, with permissions only on the regions `rd σ` and `wr σ`
(the same in both runs), on memory both runs agree on there: `memTaint`
proves it constant time from the registers `rs`, which agree. -/
theorem relMem {J : State → State → Prop} {c : Prog isa} (rd wr : State → List Region) (rs : List Reg)
    (hrw : ∀ σ₁ σ₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → rd σ₁ = rd σ₂ ∧ wr σ₁ = wr σ₂)
    (hc : ∀ σ s, Pre σ → J σ s → Covers (rd σ ++ wr σ) (s.rd ++ s.wr) ∧ Covers (wr σ) s.wr)
    (hx : ∀ σ s, Pre σ → J σ s → ∃ t s', Exec isa c (s.withRegions (rd σ) (wr σ)) t s')
    (hr : ∀ σ₁ σ₂ s₁ s₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → J σ₁ s₁ → J σ₂ s₂ →
      s₁.sp = s₂.sp ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      ∀ x, InRegions (rd σ₁ ++ wr σ₁) x 1 → s₁.mem x = s₂.mem x)
    {hint : VG.Taint.Hint memTaint.T} (h : (memTaint.check (Taint.ofRegs rs) c hint).isSome = true) :
    RelCT isa (Rel2 Pre Pub J) c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ := hP
  obtain ⟨erd, ewr⟩ := hrw σ₁ σ₂ p₁ p₂ hq
  refine RelCT.narrow (P := fun a b => a = s₁ ∧ b = s₂) (rd σ₁) (wr σ₁)
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      refine ⟨hc σ₁ a p₁ j₁, ?_⟩
      rw [erd, ewr]; exact hc σ₂ b p₂ j₂)
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      refine ⟨hx σ₁ a p₁ j₁, ?_⟩
      rw [erd, ewr]; exact hx σ₂ b p₂ j₂)
    (RelCT.taint (A := memTaint) (Taint.ofRegs rs) (fun u₁ u₂ hu => ?_) h) s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨a, b, ⟨rfl, rfl⟩, rfl, rfl⟩ := hu
  obtain ⟨hsp, hrs, hm⟩ := hr σ₁ σ₂ a b p₁ p₂ hq j₁ j₂
  exact ⟨Proof.MlKem.AArch64.agree_of hsp hrs, rfl, rfl, fun x hx => hm x hx⟩

end

end VG.Proof.MlDsa.AArch64.Sample

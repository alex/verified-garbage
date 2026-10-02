import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Base

/-!
# ML-DSA on 32-bit ARM: pieces of code, correct and constant time together

As on x86-64: a piece of code takes each run of a function, from an entry
state `σ` that satisfies its precondition `Pre`, from the invariant `I` to `J`
(`ok`), and leaks the same in two runs related by `I` whose entry states agree
on the public data `Pub` (`tr`, `Rel2`). Pieces compose (`Piece.seq`,
`Piece.seqR`), which proves correctness and constant time together.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm
open VG.Impl.MlDsa.Arm.KeyGen (seqR)

/-- Two states each related by `I` to an entry state; the entry states
satisfy `Pre` and agree by `Pub`. -/
def Rel2 (Pre : State → Prop) (Pub : State → State → Prop) (I : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ I σ₁ s₁ ∧ I σ₂ s₂

section
variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- A piece that leaks the same from states related by `I`, and takes each
run from `I` to `I'`. -/
theorem relInv {I I' : State → State → Prop} {c : Prog isa} (hw : ∀ σ s, Pre σ → I σ s → WP isa c s (I' σ))
    (ht : RelCT isa (Rel2 Pre Pub I) c fun _ _ => True) : RelCT isa (Rel2 Pre Pub I) c (Rel2 Pre Pub I') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩

/-- Constant time, from a relation of the runs from the entry states. -/
theorem relStart {c : Prog isa} {Q : State → State → Prop} (h : RelCT isa (Rel2 Pre Pub fun σ s => s = σ) c Q) :
    ConstantTime isa Pre Pub c :=
  RelCT.constantTime (RelCT.mono h (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => ⟨s₁, s₂, p₁, p₂, hp, rfl, rfl⟩) fun _ _ h => h)

/-- `c` takes each run from `I` to `J`, and leaks the same in two runs related by `I`. -/
structure Piece (Pre : State → Prop) (Pub : State → State → Prop) (I J : State → State → Prop) (c : Prog isa) :
    Prop where
  ok : ∀ σ s, Pre σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (Rel2 Pre Pub I) c fun _ _ => True

variable {I J K : State → State → Prop}

theorem Piece.seq {c₁ c₂ : Prog isa} (h₁ : Piece Pre Pub I J c₁) (h₂ : Piece Pre Pub J K c₂) :
    Piece Pre Pub I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (relInv h₁.ok h₁.tr) h₂.tr⟩

theorem Piece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : Piece Pre Pub I J c)
    (hI : ∀ σ s, Pre σ → I' σ s → I σ s) (hJ : ∀ σ s, Pre σ → J σ s → J' σ s) : Piece Pre Pub I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩)
      fun _ _ h => h⟩

theorem Piece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → Piece Pre Pub (I k) (I (k + 1)) (f k)) →
      Piece Pre Pub (I a) (I (a + n)) (seqR f a n)
  | 0, a, _ => ⟨fun _ _ _ hs => WP.block_nil hs, fun _ _ _ _ _ _ _ e₁ e₂ => by
      rw [VG.Impl.MlDsa.Arm.KeyGen.seqR, Exec.block_iff] at e₁ e₂
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
      obtain ⟨-, rfl⟩ := e₁
      obtain ⟨-, rfl⟩ := e₂
      exact ⟨rfl, trivial⟩⟩
  | n + 1, a, h => by
    have h1 := Piece.seqR (I := I) n (a + 1) fun k h₁ h₂ => h k (by omega) (by omega)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact (h a (Nat.le_refl _) (by omega)).seq (c₂ := VG.Impl.MlDsa.Arm.KeyGen.seqR f (a + 1) n) h1

/-- A piece's constant time, from a relation implied by the invariants of two runs. -/
theorem rel_of {c : Prog isa} {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (Rel2 Pre Pub I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

end

end VG.Proof.MlDsa.Arm.KeyGen

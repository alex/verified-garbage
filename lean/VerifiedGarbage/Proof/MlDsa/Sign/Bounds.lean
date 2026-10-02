import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA: the samplers are monotone in their bounds

The XOFs' output for a larger length extends the output for a smaller one
(`H_take`, `G_take`), so `RejNTTPoly`, `SampleInBall` and `ExpandA` that
finish within a bound give the same result within any larger one
(`rejNTTPoly_mono`, `sampleInBall_mono`, `expandA_mono`).
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa
open VG.Spec.Sha3 (squeeze shake128 shake256 keccak sponge)
open VG.Proof.Sha3 (length_squeeze squeeze_getElem)

theorem ifp {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifn {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-! ## The XOFs -/

/-- The first `d` bytes of a longer output. -/
theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : Spec.Sha3.State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d := by
  refine List.ext_getElem (by simp [length_squeeze hr hr']; omega) fun i h₁ h₂ => ?_
  rw [length_squeeze hr hr'] at h₂
  rw [List.getElem_take, squeeze_getElem hr hr' _ h₂, squeeze_getElem hr hr' _ (by omega)]

theorem H_length (s : List Byte) (d : Nat) : (H s d).length = d := length_squeeze (by decide) (by decide) _ _

theorem G_length (s : List Byte) (d : Nat) : (G s d).length = d := length_squeeze (by decide) (by decide) _ _

theorem H_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (H s d').take d = H s d :=
  squeeze_take (by decide) (by decide) _ h

theorem G_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (G s d').take d = G s d :=
  squeeze_take (by decide) (by decide) _ h

theorem H_extend (s : List Byte) {d d' : Nat} (h : d ≤ d') : H s d' = H s d ++ (H s d').drop d := by
  rw [← H_take s h, List.take_append_drop]

theorem G_extend (s : List Byte) {d d' : Nat} (h : d ≤ d') : G s d' = G s d ++ (G s d').drop d := by
  rw [← G_take s h, List.take_append_drop]

/-! ## `RejNTTPoly` -/

theorem rejNTTLoop_append : ∀ (a : List Zq) (out more : List Byte) (x : List Zq),
    rejNTTLoop a out = some x → rejNTTLoop a (out ++ more) = some x
  | a, s₀ :: s₁ :: s₂ :: out, more, x, h => by
    simp only [rejNTTLoop, List.cons_append] at h ⊢
    split at h
    · rw [ifp ‹_›]; exact h
    · rw [ifn ‹_›]; exact rejNTTLoop_append _ out more x h
  | a, [], more, x, h => by
    have ha : a.length ≥ n ∧ a = x := by simpa [rejNTTLoop] using h
    obtain ⟨hl, rfl⟩ := ha
    match more with
    | s₀ :: s₁ :: s₂ :: _ => simp [rejNTTLoop, hl]
    | [] => simp [rejNTTLoop, hl]
    | [_] => simp [rejNTTLoop, hl]
    | [_, _] => simp [rejNTTLoop, hl]
  | a, [s₀], more, x, h => by
    have ha : a.length ≥ n ∧ a = x := by simpa [rejNTTLoop] using h
    obtain ⟨hl, rfl⟩ := ha
    match more with
    | s₁ :: s₂ :: _ => simp [rejNTTLoop, hl]
    | [] => simp [rejNTTLoop, hl]
    | [_] => simp [rejNTTLoop, hl]
  | a, [s₀, s₁], more, x, h => by
    have ha : a.length ≥ n ∧ a = x := by simpa [rejNTTLoop] using h
    obtain ⟨hl, rfl⟩ := ha
    match more with
    | s₂ :: _ => simp [rejNTTLoop, hl]
    | [] => simp [rejNTTLoop, hl]

theorem rejNTTPoly_mono {b b' : Nat} (hb : b ≤ b') {ρ : List Byte} {x : Poly}
    (h : rejNTTPoly b ρ = some x) : rejNTTPoly b' ρ = some x := by
  unfold rejNTTPoly at h ⊢
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [G_extend ρ hb, rejNTTLoop_append _ _ _ _ ha]
  rfl

/-! ## `SampleInBall` -/

theorem ballLoop_append (τ : Nat) (hb : Array Bool) : ∀ (c : IPoly) (i : Nat) (out more : List Byte) (x : IPoly),
    ballLoop τ hb c i out = some x → ballLoop τ hb c i (out ++ more) = some x
  | c, i, [], more, x, h => by
    have hc : i ≥ n ∧ c = x := by simpa [ballLoop] using h
    obtain ⟨hi, rfl⟩ := hc
    cases more with
    | nil => simp [ballLoop, hi]
    | cons j more => simp [ballLoop, hi]
  | c, i, j :: out, more, x, h => by
    simp only [ballLoop, List.cons_append] at h ⊢
    split at h
    · rw [ifp ‹_›]; exact h
    · rw [ifn ‹_›]
      split at h
      · rw [ifp ‹_›]; exact ballLoop_append τ hb c i out more x h
      · rw [ifn ‹_›]; exact ballLoop_append τ hb _ _ out more x h

theorem sampleInBall_mono {τ b b' : Nat} (hb : b ≤ b') {ρ : List Byte} {x : IPoly}
    (h : sampleInBall τ b ρ = some x) : sampleInBall τ b' ρ = some x := by
  unfold sampleInBall at h ⊢
  have hl : ¬ (H ρ b).length < 8 := fun hl => by rw [ifp hl] at h; cases h
  rw [ifn hl] at h
  have hl' : ¬ (H ρ b').length < 8 := by rw [H_length] at hl ⊢; omega
  rw [ifn hl', H_extend ρ hb, List.take_append_of_le_length (by omega),
    List.drop_append_of_le_length (by omega)]
  exact ballLoop_append τ _ _ _ _ _ _ h

/-! ## `ExpandA` -/

theorem mapM_some_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → (∀ x ∈ l, ∀ y, f x = some y → g x = some y) →
      l.mapM g = some ys
  | [], ys, h, _ => by simpa using h
  | x :: l, ys, h, hfg => by
    rw [List.mapM_cons] at h ⊢
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys', hys, h⟩ := Option.bind_eq_some_iff.mp h
    have hl := mapM_some_congr hys fun x hx => hfg x (List.mem_cons_of_mem _ hx)
    simp only [hfg x (List.mem_cons_self ..) y hy, hl, Option.bind_eq_bind, Option.bind_some]
    exact h

theorem expandA_mono {p : Params} {b b' : Bounds} (hb : b.rejNTT ≤ b'.rejNTT) {ρ : List Byte}
    {A : List (List Poly)} (h : expandA p b ρ = some A) : expandA p b' ρ = some A := by
  unfold expandA at h ⊢
  exact mapM_some_congr h fun _ _ _ hr => mapM_some_congr hr fun _ _ _ hy => rejNTTPoly_mono hb hy

theorem minBounds_le_max : minBounds.rejNTT ≤ maxBounds.rejNTT ∧ minBounds.ball ≤ maxBounds.ball ∧
    minBounds.sign ≤ maxBounds.sign := by decide

end VG.Proof.MlDsa.Sign

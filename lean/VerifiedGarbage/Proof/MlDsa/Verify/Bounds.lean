import VerifiedGarbage.Spec.MlDsa
import VerifiedGarbage.Proof.Sha3.Stream

/-!
# ML-DSA: larger bounds give the same results

`H` and `G` squeezed to fewer bytes give a prefix of their longer outputs
(`H_take`, `G_take`), so the samplers `RejNTTPoly` and `SampleInBall`, which
stop once they have their output, give the same result from any larger bound
once they succeed (`rejNTTPoly_mono`, `sampleInBall_mono`); and so does
`verifyMu` (`verifyMu_mono`), for bounds that are larger in the two loops it
has.
-/

namespace VG.Proof.MlDsa.Verify

open VG.Spec.MlDsa
open VG.Spec.Sha3 (squeeze keccak sponge)

theorem iteP {α : Sort _} {p : Prop} [Decidable p] (h : p) {a b : α} : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem iteN {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) {a b : α} : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-- `b` bounds each loop by no more than `b'` does. -/
structure BLe (b b' : Bounds) : Prop where
  sign : b.sign ≤ b'.sign
  rejBounded : b.rejBounded ≤ b'.rejBounded
  rejNTT : b.rejNTT ≤ b'.rejNTT
  ball : b.ball ≤ b'.ball

/-- The larger of two bounds on each loop. -/
def bmax (b b' : Bounds) : Bounds :=
  ⟨max b.sign b'.sign, max b.rejBounded b'.rejBounded, max b.rejNTT b'.rejNTT, max b.ball b'.ball⟩

theorem bmax_left (b b' : Bounds) : BLe b (bmax b b') :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩

theorem bmax_right (b b' : Bounds) : BLe b' (bmax b b') :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _⟩

theorem BLe.refl (b : Bounds) : BLe b b := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem BLe.trans {a b c : Bounds} (h₁ : BLe a b) (h₂ : BLe b c) : BLe a c :=
  ⟨Nat.le_trans h₁.1 h₂.1, Nat.le_trans h₁.2 h₂.2, Nat.le_trans h₁.3 h₂.3, Nat.le_trans h₁.4 h₂.4⟩

/-! ## Prefixes of the outputs of `H` and `G` -/

theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : Spec.Sha3.State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d := by
  refine List.ext_getElem (by simp [Proof.Sha3.length_squeeze hr hr']; omega) fun i h₁ h₂ => ?_
  rw [Proof.Sha3.length_squeeze hr hr'] at h₂
  rw [List.getElem_take, Proof.Sha3.squeeze_getElem hr hr' _ h₂, Proof.Sha3.squeeze_getElem hr hr' _ (by omega)]

theorem H_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (H s d').take d = H s d :=
  squeeze_take (by decide) (by decide) _ h

theorem G_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (G s d').take d = G s d :=
  squeeze_take (by decide) (by decide) _ h

theorem H_length (s : List Byte) (d : Nat) : (H s d).length = d :=
  Proof.Sha3.length_squeeze (by decide) (by decide) _ _

/-! ## `RejNTTPoly` -/

theorem rejNTTLoop_full {a : List Zq} (ha : a.length ≥ n) : ∀ out, rejNTTLoop a out = some a
  | _ :: _ :: _ :: _ => by unfold rejNTTLoop; exact ite_eq_left_iff.mpr fun h => absurd ha h
  | [] => by unfold rejNTTLoop; exact ite_eq_left_iff.mpr fun h => absurd ha h
  | [_] => by unfold rejNTTLoop; exact ite_eq_left_iff.mpr fun h => absurd ha h
  | [_, _] => by unfold rejNTTLoop; exact ite_eq_left_iff.mpr fun h => absurd ha h

theorem rejNTTLoop_step {a : List Zq} (ha : ¬ a.length ≥ n) (s₀ s₁ s₂ : Byte) (out : List Byte) :
    rejNTTLoop a (s₀ :: s₁ :: s₂ :: out) = rejNTTLoop (match coeffFromThreeBytes s₀ s₁ s₂ with
      | some c => a ++ [c]
      | none => a) out := by
  rw [rejNTTLoop.eq_1]
  exact iteN ha

theorem rejNTTLoop_short {a : List Zq} (ha : ¬ a.length ≥ n) {out : List Byte} (h : out.length < 3) :
    rejNTTLoop a out = none := by
  match out, h with
  | [], _ => unfold rejNTTLoop; exact iteN ha
  | [_], _ => unfold rejNTTLoop; exact iteN ha
  | [_, _], _ => unfold rejNTTLoop; exact iteN ha

theorem rejNTTLoop_append : ∀ (a : List Zq) (out more : List Byte) (x : List Zq),
    rejNTTLoop a out = some x → rejNTTLoop a (out ++ more) = some x
  | a, s₀ :: s₁ :: s₂ :: out, more, x, h => by
    by_cases ha : a.length ≥ n
    · rw [rejNTTLoop_full ha] at h ⊢; exact h
    · rw [rejNTTLoop_step ha] at h
      rw [List.cons_append, List.cons_append, List.cons_append, rejNTTLoop_step ha]
      exact rejNTTLoop_append _ out more x h
  | a, [], more, x, h
  | a, [_], more, x, h
  | a, [_, _], more, x, h => by
    by_cases ha : a.length ≥ n
    · rw [rejNTTLoop_full ha] at h ⊢; exact h
    · rw [rejNTTLoop_short ha (by simp)] at h; cases h

theorem rejNTTPoly_mono {bound bound' : Nat} (hb : bound ≤ bound') {ρ : List Byte} {x : Poly}
    (h : rejNTTPoly bound ρ = some x) : rejNTTPoly bound' ρ = some x := by
  unfold rejNTTPoly at h ⊢
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  have e : G ρ bound' = G ρ bound ++ (G ρ bound').drop bound := by
    rw [← G_take ρ hb, List.take_append_drop]
  rw [e, rejNTTLoop_append _ _ _ _ ha]
  rfl

/-! ## `SampleInBall` -/

theorem ballLoop_full (τ : Nat) (h : Array Bool) {c : IPoly} {i : Nat} (hi : i ≥ n) :
    ∀ out, ballLoop τ h c i out = some c
  | [] => by rw [ballLoop.eq_1]; exact iteP hi
  | _ :: _ => by rw [ballLoop.eq_2]; exact iteP hi

theorem ballLoop_step (τ : Nat) (h : Array Bool) {c : IPoly} {i : Nat} (hi : ¬ i ≥ n) (j : Byte)
    (out : List Byte) : ballLoop τ h c i (j :: out) =
      if j.toNat > i then ballLoop τ h c i out
      else ballLoop τ h ((c.set! i c[j.toNat]!).set! j.toNat (if h.getD (i + τ - 256) false then -1 else 1))
        (i + 1) out := by
  rw [ballLoop.eq_2]; exact iteN hi

theorem ballLoop_append (τ : Nat) (h : Array Bool) : ∀ (out more : List Byte) (c : IPoly) (i : Nat) (x : IPoly),
    ballLoop τ h c i out = some x → ballLoop τ h c i (out ++ more) = some x
  | [], more, c, i, x, e => by
    by_cases hi : i ≥ n
    · rw [ballLoop_full τ h hi] at e ⊢; exact e
    · rw [ballLoop.eq_1, iteN hi] at e; cases e
  | j :: out, more, c, i, x, e => by
    by_cases hi : i ≥ n
    · rw [ballLoop_full τ h hi] at e ⊢; exact e
    · rw [ballLoop_step τ h hi] at e
      rw [List.cons_append, ballLoop_step τ h hi]
      split at e
      · rw [iteP ‹_›]; exact ballLoop_append τ h out more _ _ _ e
      · rw [iteN ‹_›]; exact ballLoop_append τ h out more _ _ _ e

theorem sampleInBall_mono {τ bound bound' : Nat} (hb : bound ≤ bound') {ρ : List Byte} {x : IPoly}
    (h : sampleInBall τ bound ρ = some x) : sampleInBall τ bound' ρ = some x := by
  unfold sampleInBall at h ⊢
  dsimp only at h ⊢
  rw [H_length] at h ⊢
  split at h
  · cases h
  · rename_i h8
    rw [iteN (by omega)]
    have e : H ρ bound' = H ρ bound ++ (H ρ bound').drop bound := by
      rw [← H_take ρ hb, List.take_append_drop]
    have e8 : (H ρ bound').take 8 = (H ρ bound).take 8 := by
      rw [e, List.take_append_of_le_length (by rw [H_length]; omega)]
    have ed := congrArg (List.drop 8) e
    rw [List.drop_append_of_le_length (by rw [H_length]; omega)] at ed
    rw [e8, ed]
    exact ballLoop_append _ _ _ _ _ _ _ h

/-! ## `ExpandA` and `verifyMu` -/

theorem mapM_mono {α β : Type} {f f' : α → Option β}
    (hf : ∀ a y, f a = some y → f' a = some y) : ∀ {l : List α} {ys : List β},
    l.mapM f = some ys → l.mapM f' = some ys
  | [], _, h => h
  | a :: l, ys, h => by
    rw [List.mapM_cons] at h ⊢
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys', hys, h⟩ := Option.bind_eq_some_iff.mp h
    rw [hf a y hy, mapM_mono hf hys]
    exact h

theorem expandA_mono {p : Params} {b b' : Bounds} (hb : b.rejNTT ≤ b'.rejNTT) {ρ : List Byte}
    {A : List (List Poly)} (h : expandA p b ρ = some A) : expandA p b' ρ = some A :=
  mapM_mono (fun _ _ hr => mapM_mono (fun _ _ hs => rejNTTPoly_mono hb hs) hr) h

theorem verifyMu_mono {p : Params} {b b' : Bounds} (h₁ : b.rejNTT ≤ b'.rejNTT) (h₂ : b.ball ≤ b'.ball)
    {pk μ σ : List Byte} {x : Bool} (h : verifyMu p b pk μ σ = some x) : verifyMu p b' pk μ σ = some x := by
  unfold verifyMu at h ⊢
  generalize pkDecode p pk = PK at h ⊢
  obtain ⟨ρ, t₁⟩ := PK
  generalize sigDecode p σ = SD at h ⊢
  obtain ⟨ct, z, ho⟩ := SD
  cases ho with
  | none => exact h
  | some hh =>
    dsimp only at h ⊢
    obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    rw [expandA_mono h₁ hA, sampleInBall_mono h₂ hc]
    exact h

/-! ## The postcondition of verification -/

/-- The postcondition of `verifyContract`, from the value of `verifyMu` for
some bounds: a result of 1 if it is true, and 0 if it is false. -/
theorem post_of_value {v : Bounds → Option Bool}
    (hv : ∀ b b' x, b.rejNTT ≤ b'.rejNTT → b.ball ≤ b'.ball → v b = some x → v b' = some x)
    {b : Bounds} {x : Bool} (h : v b = some x) (r : BitVec 32) (hr : r = if x then 1 else 0) :
    (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true) := by
  cases x
  · refine .inr ⟨hr, fun hm => ?_⟩
    have e₁ := hv _ _ _ (bmax_left b minBounds).rejNTT (bmax_left b minBounds).ball h
    have e₂ := hv _ _ _ (bmax_right b minBounds).rejNTT (bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂
  · exact .inl ⟨hr, b, h⟩

end VG.Proof.MlDsa.Verify

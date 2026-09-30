import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked

/-!
# ML-DSA key generation: the result of the samplers, for every target

Untrusted: everything here is checked by Lean. Key generation samples every
entry of `Â` and of `s₁ ‖ s₂`, and ANDs the results of the samplers
(`RejNTTPoly`, `RejBoundedPoly`, which may stop at their bounds) without
branching on them. `Good` says what the AND is after the first `e` entries
of `Â` and `r` of `s₁ ‖ s₂`: 1, with the entries those of the standard for
some bounds, or 0 if key generation fails within the least bounds. Each
sampler's outcome, ANDed in, keeps it (`good_A`, `good_S`), with the entry
stored masked by the result (`masked_one`, `masked_zero`); and at the end it
is the outcome of key generation (`outcome_keyGen`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

/-- The AND of the results so far, after the first `e` entries of `Â` and `r`
of `s₁ ‖ s₂` of key generation from `ξ`. -/
def Good (p : Params) (ξ : List Byte) (e r : Nat) (A : Nat → Poly) (S : Nat → IPoly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ b : Bounds,
      (∀ e' < e, rejNTTPoly b.rejNTT (seedA (keyGenSeeds p ξ).1 (e' / p.ℓ) (e' % p.ℓ)) = some (A e')) ∧
      ∀ r' < r, rejBoundedPoly p.η b.rejBounded (seedS (keyGenSeeds p ξ).2.1 r') = some (S r')) ∨
    (v = 0 ∧ keyGenInternal p minBounds ξ = none)

theorem good_01 {p : Params} {ξ : List Byte} {e r : Nat} {A : Nat → Poly} {S : Nat → IPoly} {v : BitVec 32}
    (h : Good p ξ e r A S v) : v = 0 ∨ v = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

theorem good_zero (p : Params) (ξ : List Byte) (A : Nat → Poly) (S : Nat → IPoly) : Good p ξ 0 0 A S 1 :=
  .inl ⟨rfl, ⟨0, 0, 0, 0⟩, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem and_01 {v r : BitVec 32} (hv : v = 0 ∨ v = 1) (hr : r = 0 ∨ r = 1) :
    v &&& r = if v = 1 ∧ r = 1 then 1 else 0 := by
  rcases hv with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

/-- An entry of `Â`, sampled: `y` is what is stored, the output if the
sampler succeeded. -/
theorem good_A {p : Params} {ξ : List Byte} {e : Nat} (he : e < p.k * p.ℓ) {A : Nat → Poly} {S : Nat → IPoly}
    {v r : BitVec 32} {x y : Poly} (hG : Good p ξ e 0 A S v)
    (ho : Outcome (fun b => rejNTTPoly b.rejNTT (seedA (keyGenSeeds p ξ).1 (e / p.ℓ) (e % p.ℓ))) r x)
    (hy : r = 1 → y = x) :
    Good p ξ (e + 1) 0 (fun e' => if e' = e then y else A e') S (v &&& r) := by
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at he; exact Nat.not_lt_zero _ he
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ hl
  rw [and_01 (good_01 hG) (outcome_01 ho)]
  rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
  · rcases ho with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
    · refine .inl ⟨by rw [ifp ⟨h1, ho⟩], bmax b b', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      dsimp only
      rcases (by omega : e' < e ∨ e' = e) with he' | rfl
      · rw [ifn (by omega)]
        exact rejNTTPoly_mono (Bounds.le_max_left b b').rejNTT (hb e' he')
      · rw [ifp rfl, hy ho]
        exact rejNTTPoly_mono (Bounds.le_max_right b b').rejNTT hb'
    · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
      exact .inr ⟨rfl, keyGenInternal_none_A hq hr hn⟩
  · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
    exact .inr ⟨rfl, hn⟩

/-- An entry of `s₁ ‖ s₂`, sampled: what is stored is `toRq z` for a small `z`,
the output if the sampler succeeded. -/
theorem good_S {p : Params} {ξ : List Byte} {r : Nat} (hr : r < p.ℓ + p.k) {A : Nat → Poly} {S : Nat → IPoly}
    {v res : BitVec 32} {x : Poly}
    (hG : Good p ξ (p.k * p.ℓ) r A S v)
    (ho : Outcome (fun b => (rejBoundedPoly p.η b.rejBounded (seedS (keyGenSeeds p ξ).2.1 r)).map toRq) res x) :
    ∃ z : IPoly, Small p.η z ∧ (res = 1 → toRq z = x) ∧ (res ≠ 1 → z = Vector.replicate 256 0) ∧
      Good p ξ (p.k * p.ℓ) (r + 1) A (fun r' => if r' = r then z else S r') (v &&& res) := by
  rw [and_01 (good_01 hG) (outcome_01 ho)]
  by_cases h1 : res = 1
  · obtain ⟨b', hb'⟩ : ∃ b' : Bounds, (rejBoundedPoly p.η b'.rejBounded (seedS (keyGenSeeds p ξ).2.1 r)).map toRq =
        some x := by
      rcases ho with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · rw [h] at h1; exact absurd h1 (by decide)
    obtain ⟨z, hz, htz⟩ := Option.map_eq_some_iff.mp hb'
    refine ⟨z, rejBoundedPoly_range hz, fun _ => htz, fun h => absurd h1 h, ?_⟩
    rcases hG with ⟨hv, b, hbA, hbS⟩ | ⟨h0, hn⟩
    · refine .inl ⟨by rw [ifp ⟨hv, h1⟩], bmax b b', fun e' he' =>
        rejNTTPoly_mono (Bounds.le_max_left b b').rejNTT (hbA e' he'), fun r' hr' => ?_⟩
      dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [ifn (by omega)]
        exact rejBoundedPoly_mono (Bounds.le_max_left b b').rejBounded (hbS r' hr')
      · rw [ifp rfl]
        exact rejBoundedPoly_mono (Bounds.le_max_right b b').rejBounded hz
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl, hn⟩
  · have hn : rejBoundedPoly p.η minBounds.rejBounded (seedS (keyGenSeeds p ξ).2.1 r) = none := by
      rcases ho with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h h1
      · exact Option.map_eq_none_iff.mp h
    refine ⟨Vector.replicate 256 0, small_zero _, fun h => absurd h h1, fun _ => rfl, ?_⟩
    rw [ifn (fun h => h1 h.2)]
    exact .inr ⟨rfl, keyGenInternal_none_S hr hn⟩

theorem idx_lt {p : Params} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have : p.ℓ * i + j < p.ℓ * (i + 1) := by rw [Nat.mul_succ]; omega
  have : p.ℓ * (i + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ hi
  rw [Nat.mul_comm p.k]; omega

/-- At the end, the AND of the results is the outcome of key generation. -/
theorem outcome_keyGen {p : Params} {ξ : List Byte} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 32}
    (hl : 0 < p.ℓ) (hG : Good p ξ (p.k * p.ℓ) (p.ℓ + p.k) A S R) :
    Outcome (fun b => keyGenInternal p b ξ) R
      (pkK p A S (keyGenSeeds p ξ).1, skK p A S (keyGenSeeds p ξ).1 (keyGenSeeds p ξ).2.2) := by
  rcases hG with ⟨rfl, b, hbA, hbS⟩ | ⟨rfl, hn⟩
  · refine .inl ⟨rfl, b, ?_⟩
    show keyGenInternal p b ξ = _
    rw [keyGenInternal_eq, expandA_some (A := fun r s => A (p.ℓ * r + s)) fun r hr s hs => ?_, Option.bind_some,
      expandS_some (S := S) hbS, Option.map_some, kgRest_eq]
    have := hbA (p.ℓ * r + s) (idx_lt hr hs)
    rwa [Nat.mul_add_div hl, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs] at this
  · exact .inr ⟨rfl, hn⟩

/-! ## A masked polynomial -/

end VG.Proof.MlDsa.KeyGen

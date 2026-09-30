import VerifiedGarbage.Proof.MlDsa.Sign.Bounds

/-!
# ML-DSA: the signing loop

Untrusted: everything here is checked by Lean. An iteration of the signing
loop (`signIteration`) is its commitment, `SampleInBall` of its `c̃`, and
the validity checks (`iterOut`), all computed from `c` (`signIteration_eq`):
so it depends on the bounds only through `SampleInBall`, and a larger bound
gives the same result once a smaller one finishes (`signIteration_mono`,
`signIteration_min`). The loop (`signLoop`) returns the first iteration that
passes after iterations that were rejected (`signLoop_pass`), and nothing if
all of them were rejected (`signLoop_exhaust`); within smaller bounds, it
returns nothing if the larger bounds reject every iteration before one
whose `SampleInBall` does not finish within the smaller ones
(`signLoop_min_none`).
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa

section
variable (p : Params) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly) (μ ρ'' : List Byte)

/-- What an iteration computes once `c` is sampled: `(z, h)` if the
validity checks pass (lines 17–30 of Algorithm 7). -/
def iterOut (y : List IPoly) (w : List Poly) (c : IPoly) : Option (List Poly × List (Vector Bool n)) :=
  let ĉ := ntt (toRq c)
  let cs₁ := ŝ₁.map fun s => nttInv (multiplyNTT ĉ s)
  let cs₂ := ŝ₂.map fun s => nttInv (multiplyNTT ĉ s)
  let z := addVec (y.map toRq) cs₁
  let r₀ := (subVec w cs₂).map fun ri => ri.map (lowBits p.γ₂)
  let ct₀ := t₀Hat.map fun t => nttInv (multiplyNTT ĉ t)
  let h := List.zipWith (fun u v => Vector.zipWith (makeHint p.γ₂) u v)
    (ct₀.map neg) (addVec (subVec w cs₂) ct₀)
  let ones := (h.map fun hi => (hi.toList.filter id).length).sum
  if normRq z ≥ p.γ₁ - p.β ∨ normR r₀ ≥ p.γ₂ - p.β ∨ normRq ct₀ ≥ p.γ₂ ∨ ones > p.ω then none
  else some (z, h)

/-- An iteration: its `c̃` and, if `SampleInBall` finishes, the outcome of its checks. -/
theorem signIteration_eq (b : Bounds) (κ : Nat) :
    signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ =
      (sampleInBall p.τ b.ball (signCommit p Â μ ρ'' κ).2.2).map fun c =>
        ((signCommit p Â μ ρ'' κ).2.2,
          iterOut p ŝ₁ ŝ₂ t₀Hat (signCommit p Â μ ρ'' κ).1 (signCommit p Â μ ρ'' κ).2.1 c) := by
  unfold signIteration iterOut
  rcases signCommit p Â μ ρ'' κ with ⟨y, w, ct⟩
  dsimp only
  cases sampleInBall p.τ b.ball ct with
  | none => rfl
  | some c =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    by_cases h1 : normRq (addVec (y.map toRq) (ŝ₁.map fun s => nttInv (multiplyNTT (ntt (toRq c)) s))) ≥ p.γ₁ - p.β ∨
      normR ((subVec w (ŝ₂.map fun s => nttInv (multiplyNTT (ntt (toRq c)) s))).map fun ri => ri.map (lowBits p.γ₂)) ≥
        p.γ₂ - p.β
    · rw [ifp h1, ifp (h1.elim Or.inl fun h => Or.inr (Or.inl h))]; rfl
    · rw [ifn h1]
      split
      · rename_i h2; rw [ifp (by omega)]; rfl
      · rename_i h2; rw [ifn (by omega)]; rfl

theorem signIteration_mono {b b' : Bounds} (hb : b.ball ≤ b'.ball) {κ : Nat}
    {r : List Byte × Option (List Poly × List (Vector Bool n))}
    (h : signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = some r) : signIteration p b' Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = some r := by
  rw [signIteration_eq] at h ⊢
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [sampleInBall_mono hb hc]; rfl

/-- Within a smaller bound, an iteration either does not finish or has the same outcome. -/
theorem signIteration_min {b b' : Bounds} (hb : b.ball ≤ b'.ball) {κ : Nat}
    {r : List Byte × Option (List Poly × List (Vector Bool n))}
    (h : signIteration p b' Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = some r) :
    signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = none ∨ signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = some r := by
  cases e : signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
  | none => exact .inl rfl
  | some r' => rw [signIteration_mono p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' hb e] at h; exact .inr (congrArg some (Option.some.inj h))

/-! ## The loop -/

theorem signLoop_succ (b : Bounds) (n κ : Nat) :
    signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (n + 1) κ =
      match signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
      | none => none
      | some (ct, some (z, h)) => some (ct, z, h)
      | some (_, none) => signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n (κ + p.ℓ) := by
  simp only [signLoop, Option.bind_eq_bind]
  cases signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
  | none => rfl
  | some r =>
    obtain ⟨ct, o⟩ := r
    cases o with
    | none => rfl
    | some zh => rfl

/-- The `i` iterations from the counter `κ` are rejected within the bounds `b`. -/
def Rej (b : Bounds) (κ i : Nat) : Prop :=
  ∀ j < i, ∃ ct, signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (κ + p.ℓ * j) = some (ct, none)

theorem Rej.succ {b : Bounds} {κ i : Nat} (h : Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b κ i) {ct : List Byte}
    (hi : signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (κ + p.ℓ * i) = some (ct, none)) :
    Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b κ (i + 1) := fun j hj => by
  rcases (by omega : j < i ∨ j = i) with hj | rfl
  exacts [h j hj, ⟨ct, hi⟩]

theorem Rej.tail {b : Bounds} {κ i : Nat} (h : Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b κ (i + 1)) :
    Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b (κ + p.ℓ) i := fun j hj => by
  obtain ⟨ct, hc⟩ := h (j + 1) (by omega)
  exact ⟨ct, by rw [show κ + p.ℓ + p.ℓ * j = κ + p.ℓ * (j + 1) by rw [Nat.mul_succ]; omega]; exact hc⟩

/-- Rejected iterations are skipped. -/
theorem signLoop_rej {b : Bounds} : ∀ {i κ n : Nat}, Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b κ i → i ≤ n →
    signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n κ = signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (n - i) (κ + p.ℓ * i)
  | 0, κ, n, _, _ => by simp
  | i + 1, κ, n + 1, h, hi => by
    obtain ⟨ct, hc⟩ := h 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at hc
    rw [signLoop_succ, hc]
    dsimp only
    rw [signLoop_rej h.tail (by omega), show n + 1 - (i + 1) = n - i by omega,
      show κ + p.ℓ + p.ℓ * i = κ + p.ℓ * (i + 1) by rw [Nat.mul_succ]; omega]
  | _ + 1, _, 0, _, hi => absurd hi (by omega)

theorem signLoop_pass {b : Bounds} {i N : Nat} (h : Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b 0 i) (hi : i < N)
    {ct : List Byte} {z : List Poly} {hh : List (Vector Bool n)}
    (hp : signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (p.ℓ * i) = some (ct, some (z, hh))) :
    signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' N 0 = some (ct, z, hh) := by
  rw [signLoop_rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' h (by omega), Nat.zero_add,
    show N - i = (N - i - 1) + 1 by omega, signLoop_succ, hp]

theorem signLoop_exhaust {b : Bounds} {n : Nat} (h : Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b 0 n) :
    signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n 0 = none := by
  rw [signLoop_rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' h (Nat.le_refl _), Nat.sub_self]; rfl

/-- Within smaller bounds `b`, the loop returns nothing if the larger bounds
`b'` reject the `i` iterations from `κ`, and the loop ends within them or at
an iteration whose `SampleInBall` does not finish within `b`. -/
theorem signLoop_min_none {b b' : Bounds} (hb : b.ball ≤ b'.ball) :
    ∀ {i κ n : Nat}, Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b' κ i →
      (n ≤ i ∨ signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (κ + p.ℓ * i) = none) →
      signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n κ = none
  | _, _, 0, _, _ => rfl
  | 0, κ, n + 1, _, hs => by
    rcases hs with hs | hs
    · omega
    · rw [Nat.mul_zero, Nat.add_zero] at hs; rw [signLoop_succ, hs]
  | i + 1, κ, n + 1, h, hs => by
    obtain ⟨ct, hc⟩ := h 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at hc
    rw [signLoop_succ]
    rcases signIteration_min p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' hb hc with e | e
    · rw [e]
    · rw [e]
      dsimp only
      refine signLoop_min_none hb h.tail ?_
      rcases hs with hs | hs
      · exact .inl (by omega)
      · exact .inr (by rw [show κ + p.ℓ + p.ℓ * i = κ + p.ℓ * (i + 1) by rw [Nat.mul_succ]; omega]; exact hs)

end

/-! ## `Sign_internal` -/

/-- Algorithm 7 with `μ` given, as the matrix and the loop. -/
theorem signMu_eq (p : Params) (b : Bounds) (sk μ rnd : List Byte) :
    signMu p b sk μ rnd =
      (expandA p b (skDecode p sk).1).bind fun Â =>
        (signLoop p b Â ((skDecode p sk).2.2.2.1.map fun s => ntt (toRq s))
          ((skDecode p sk).2.2.2.2.1.map fun s => ntt (toRq s)) ((skDecode p sk).2.2.2.2.2.map fun t => ntt (toRq t))
          μ (H ((skDecode p sk).2.1 ++ rnd ++ μ) 64) b.sign 0).map fun r =>
          sigEncode p r.1 (r.2.1.map fun zi => zi.map fun c => modPm c.val q) r.2.2 := by
  unfold signMu
  rcases skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  dsimp only
  cases expandA p b ρ with
  | none => rfl
  | some Â =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases signLoop p b Â (s₁.map fun s => ntt (toRq s)) (s₂.map fun s => ntt (toRq s)) (t₀.map fun t => ntt (toRq t))
      μ (H (K ++ rnd ++ μ) 64) b.sign 0 with
    | none => rfl
    | some r => rfl

end VG.Proof.MlDsa.Sign

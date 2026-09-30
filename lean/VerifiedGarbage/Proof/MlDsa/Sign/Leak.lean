import VerifiedGarbage.Proof.MlDsa.Sign.Loop

/-!
# ML-DSA: what signing leaks, iteration by iteration

Untrusted: everything here is checked by Lean.

`signLeakLoop` (`Spec/MlDsa/Contract.lean`) lists the commitment hash `c̃`
of each iteration of the signing loop, then the hint of the one that
passes. That list does not determine where each iteration ends: after a
`c̃`, a rejected iteration continues with the next `c̃` (`λ/4` numbers),
the passing one ends with its hint (`256k` numbers of 0 and 1), and one
whose `SampleInBall` does not finish ends the list. As `256k = 32 · λ/4`
in every parameter set, a hint of an iteration that passes reads as the
`c̃`s of 32 more iterations, the last of which does not finish, whenever
those `c̃`s consist of 0s and 1s that match the hint. Two runs with such
inputs agree on `signLeak` but run different numbers of iterations, so no
implementation that stops when its loop does meets `signContract`'s
constant-time obligation for them (they exist, as far as anyone can tell,
though no one can find them).

`signLeakLoopT` is the same list with a number after each `c̃` that says
how the iteration ended (0: rejected, 1: passed, nothing: `SampleInBall`
did not finish), which determines the structure of the loop: two runs that
agree on it agree on each `c̃`, on the outcome of each iteration and on the
hint of the one that passes (`leakT_step`).
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa

/-- `signLeakLoop`, with the outcome of each iteration after its `c̃`: 0 if
it is rejected, 1 (then its hint) if it passes. -/
def signLeakLoopT (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) : (iters κ : Nat) → List Nat
  | 0, _ => []
  | iters + 1, κ =>
    leakBytes (signCommit p Â μ ρ'' κ).2.2 ++
      match signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
      | some (_, none) => 0 :: signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters (κ + p.ℓ)
      | some (_, some (_, h)) => 1 :: h.flatMap fun hi => hi.toList.map Bool.toNat
      | none => []

/-- `signLeak`, with `signLeakLoopT` for `signLeakLoop`. -/
def signLeakT (p : Params) (sk μ rnd : List Byte) : List Nat :=
  let (ρ, K, _tr, s₁, s₂, t₀) := skDecode p sk
  leakBytes ρ ++
    match expandA p maxBounds ρ with
    | none => []
    | some Â =>
      signLeakLoopT p maxBounds Â (s₁.map fun s => ntt (toRq s)) (s₂.map fun s => ntt (toRq s))
        (t₀.map fun t => ntt (toRq t)) μ (H (K ++ rnd ++ μ) 64) maxBounds.sign 0

/-- `signLeakLoopT` is the contract's `signLeakLoop`, which tags each
iteration the same way. -/
theorem signLeakLoopT_eq_signLeakLoop (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) : ∀ iters κ,
    signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters κ = signLeakLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters κ
  | 0, _ => rfl
  | iters + 1, κ => by
    have ih := signLeakLoopT_eq_signLeakLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters (κ + p.ℓ)
    unfold signLeakLoopT signLeakLoop
    cases signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
    | none => rfl
    | some r =>
      rcases r with ⟨_, _ | _⟩
      · exact congrArg (_ ++ 0 :: ·) ih
      · rfl

/-- `signLeakT` is the contract's `signLeak`. -/
theorem signLeakT_eq_signLeak (p : Params) (sk μ rnd : List Byte) : signLeakT p sk μ rnd = signLeak p sk μ rnd := by
  have h : @signLeakLoopT = @signLeakLoop := by
    funext p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters κ
    exact signLeakLoopT_eq_signLeakLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters κ
  unfold signLeakT signLeak
  simp only [h]
  -- The two sides differ only in their `match` auxiliaries, which are equal.
  cases expandA p maxBounds (skDecode p sk).fst <;> rfl

theorem leakBytes_inj : ∀ {a b : List Byte}, leakBytes a = leakBytes b → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [leakBytes, List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, leakBytes_inj h.2]
  | [], _ :: _, h => by simp [leakBytes] at h
  | _ :: _, [], h => by simp [leakBytes] at h

theorem leakBytes_length (a : List Byte) : (leakBytes a).length = a.length := List.length_map _

/-- How an iteration ended, as `signLeakLoopT` lists it after its `c̃`. -/
def outTag : Option (List Byte × Option (List Poly × List (Vector Bool n))) → List Nat
  | some (_, none) => [0]
  | some (_, some (_, h)) => 1 :: h.flatMap fun hi => hi.toList.map Bool.toNat
  | none => []

theorem signCommit_length (p : Params) (Â : List (List Poly)) (μ ρ'' : List Byte) (κ : Nat) :
    (signCommit p Â μ ρ'' κ).2.2.length = p.ctildeLen := H_length _ _

section
variable {p : Params} {b : Bounds}
  {Â₁ Â₂ : List (List Poly)} {s₁ s₁' t₁ s₂ s₂' t₂ : List Poly} {μ₁ μ₂ ρ₁ ρ₂ : List Byte}

/-- Two runs that agree on what an iteration leaks agree on its `c̃`, on
whether it finished, was rejected or passed, and on the hint if it passed;
and, if it was rejected, on what the following iterations leak. -/
theorem leakT_step {n κ : Nat}
    (h : signLeakLoopT p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ (n + 1) κ = signLeakLoopT p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ (n + 1) κ) :
    (signCommit p Â₁ μ₁ ρ₁ κ).2.2 = (signCommit p Â₂ μ₂ ρ₂ κ).2.2 ∧
      ((∃ ct, signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ = some (ct, none)) →
        (∃ ct, signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ = some (ct, none)) ∧
        signLeakLoopT p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ n (κ + p.ℓ) = signLeakLoopT p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ n (κ + p.ℓ)) ∧
      outTag (signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ) = outTag (signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ) := by
  simp only [signLeakLoopT] at h
  have hl : (leakBytes (signCommit p Â₁ μ₁ ρ₁ κ).2.2).length = (leakBytes (signCommit p Â₂ μ₂ ρ₂ κ).2.2).length := by
    rw [leakBytes_length, leakBytes_length, signCommit_length, signCommit_length]
  obtain ⟨hc, hr⟩ := List.append_inj h hl
  refine ⟨leakBytes_inj hc, ?_, ?_⟩
  · rintro ⟨ct, e₁⟩
    rw [e₁] at hr
    dsimp only at hr
    cases e₂ : signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ with
    | none => rw [e₂] at hr; cases hr
    | some r =>
      obtain ⟨ct', o⟩ := r
      rw [e₂] at hr
      cases o with
      | none => exact ⟨⟨ct', rfl⟩, List.cons.inj hr |>.2⟩
      | some zh => cases (List.cons.inj hr).1
  · revert hr
    cases signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ with
    | none =>
      cases signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ with
      | none => intro; rfl
      | some r => obtain ⟨_, o⟩ := r; cases o <;> intro hr <;> cases hr
    | some r =>
      obtain ⟨_, o⟩ := r
      cases signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ with
      | none => cases o <;> intro hr <;> cases hr
      | some r' =>
        obtain ⟨_, o'⟩ := r'
        cases o with
        | none =>
          cases o' with
          | none => intro; rfl
          | some _ => intro hr; cases (List.cons.inj hr).1
        | some zh =>
          cases o' with
          | none => intro hr; cases (List.cons.inj hr).1
          | some zh' => intro hr; simp only [outTag]; exact hr

end

theorem signLeakLoopT_succ (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) (n κ : Nat) :
    signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (n + 1) κ =
      leakBytes (signCommit p Â μ ρ'' κ).2.2 ++
        match signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
        | some (_, none) => 0 :: signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n (κ + p.ℓ)
        | some (_, some (_, h)) => 1 :: h.flatMap fun hi => hi.toList.map Bool.toNat
        | none => [] := rfl

end VG.Proof.MlDsa.Sign

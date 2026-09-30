import VerifiedGarbage.Proof.MlDsa.Verify.Norm

/-!
# ML-DSA: when verification fails

Untrusted: everything here is checked by Lean. `verifyMu` is false when the
hint is malformed (`verifyMu_hint_none`), not true when `‖z‖∞` is too large
(`verifyMu_norm`), and `none` when a sampler does not finish within its
bound (`verifyMu_rej_none`, `verifyMu_ball_none`); and bounds for each
entry of `Â` give one bound for all of them (`common_bound`).
-/

namespace VG.Proof.MlDsa.Verify

open VG.Spec.MlDsa

theorem verifyMu_hint_none {p : Params} (b : Bounds) (pk μ : List Byte) {σ : List Byte} (hh : vHint p σ = none) :
    verifyMu p b pk μ σ = some false := by
  unfold verifyMu
  rw [pkDecode_eq, sigDecode_eq, hh]
  rfl

theorem verifyMu_eq {p : Params} (b : Bounds) (pk μ : List Byte) {σ : List Byte} {h : List (Vector Bool n)}
    (hh : vHint p σ = some h) :
    ∃ f : List (List Poly) → IPoly → Bool,
      verifyMu p b pk μ σ = (expandA p b (vRho pk)).bind fun A => (sampleInBall p.τ b.ball (vCt p σ)).bind
        fun c => some (decide (normR ((List.range p.ℓ).map (vZ p σ)) < p.γ₁ - p.β) && f A c) := by
  unfold verifyMu
  rw [pkDecode_eq, sigDecode_eq, hh]
  exact ⟨_, rfl⟩

theorem verifyMu_norm {p : Params} (b : Bounds) (pk μ : List Byte) {σ : List Byte} {h : List (Vector Bool n)}
    (hh : vHint p σ = some h) (hn : ¬ normR ((List.range p.ℓ).map (vZ p σ)) < p.γ₁ - p.β) :
    verifyMu p b pk μ σ ≠ some true := by
  obtain ⟨f, e⟩ := verifyMu_eq b pk μ hh
  rw [e]
  cases expandA p b (vRho pk) with
  | none => simp
  | some A =>
    cases sampleInBall p.τ b.ball (vCt p σ) with
    | none => simp
    | some c => simp [hn]

theorem mapM_none {α β : Type} {f : α → Option β} : ∀ {l : List α}, (∃ a ∈ l, f a = none) → l.mapM f = none
  | [], ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | a :: l, ⟨x, hx, hn⟩ => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hn]; rfl
    · cases f a with
      | none => rfl
      | some y => rw [mapM_none ⟨x, hx, hn⟩]; rfl

theorem verifyMu_rej_none {p : Params} (b : Bounds) (pk μ : List Byte) {σ : List Byte} {h : List (Vector Bool n)}
    (hh : vHint p σ = some h) {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ)
    (hn : rejNTTPoly b.rejNTT (aSeed pk r c) = none) : verifyMu p b pk μ σ = none := by
  obtain ⟨f, e⟩ := verifyMu_eq b pk μ hh
  have hA : expandA p b (vRho pk) = none :=
    mapM_none ⟨r, List.mem_range.mpr hr, mapM_none ⟨c, List.mem_range.mpr hc, hn⟩⟩
  rw [e, hA]
  rfl

theorem verifyMu_ball_none {p : Params} (b : Bounds) (pk μ : List Byte) {σ : List Byte} {h : List (Vector Bool n)}
    (hh : vHint p σ = some h) (hn : sampleInBall p.τ b.ball (vCt p σ) = none) : verifyMu p b pk μ σ = none := by
  obtain ⟨f, e⟩ := verifyMu_eq b pk μ hh
  rw [e]
  cases expandA p b (vRho pk) with
  | none => rfl
  | some A => rw [Option.bind_some, hn]; rfl

/-- A bound for each of finitely many monotone facts gives one for all. -/
theorem common_bound {P : Nat → Nat → Prop} (hm : ∀ i n n', n ≤ n' → P i n → P i n') :
    ∀ K, (∀ i < K, ∃ n, P i n) → ∃ n, ∀ i < K, P i n
  | 0, _ => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | K + 1, h => by
    obtain ⟨n, hn⟩ := common_bound hm K fun i hi => h i (by omega)
    obtain ⟨n', hn'⟩ := h K (by omega)
    refine ⟨max n n', fun i hi => ?_⟩
    rcases (by omega : i < K ∨ i = K) with hi | rfl
    · exact hm i _ _ (Nat.le_max_left _ _) (hn i hi)
    · exact hm i _ _ (Nat.le_max_right _ _) hn'

end VG.Proof.MlDsa.Verify

import VerifiedGarbage.Proof.MlDsa.Sign.Setup

/-!
# ML-DSA: signing's values, from its inputs

Untrusted: everything here is checked by Lean. What signing computes, as
functions of its inputs `sk`, `μ` and `rnd` (`Av`, `ctV`, `cV`, `passV`,
`zV`, `hV`, …), for an implementation that computes them one polynomial
at a time; and the loop of an implementation whose `SampleInBall` succeeds
exactly when `ballF` says, and which succeeds only when the algorithm
finishes within `maxBounds` (`BallF`): iteration `t` continues the loop
(`contV`) if its `SampleInBall` succeeded and its checks failed, and the
loop runs `nIt contV 814` iterations.

Two runs whose `signLeakT` agree agree on `ρ` (`rho_of_leak`), and, once
`ExpandA` finishes, on what each iteration they both reach leaks
(`leak_iter`): its `c̃`, whether its checks passed, and then its hint.
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa

/-! ## The number of iterations -/

/-- The number of iterations of a loop of at most `M` iterations that
continues after iteration `t` while `f t`. -/
def nIt (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | M + 1 => if (List.range M).all f then M + 1 else nIt f M

theorem nIt_le (f : Nat → Bool) : ∀ M, nIt f M ≤ M
  | 0 => Nat.le_refl _
  | M + 1 => by
    unfold nIt
    split
    · exact Nat.le_refl _
    · have := nIt_le f M; omega

theorem nIt_pos (f : Nat → Bool) : ∀ {M}, 0 < M → 0 < nIt f M
  | 0, h => absurd h (Nat.lt_irrefl _)
  | M + 1, _ => by
    unfold nIt
    split
    · omega
    · rename_i h
      cases M with
      | zero => exact absurd (by simp) h
      | succ M => exact nIt_pos f (Nat.succ_pos M)

theorem nIt_cont (f : Nat → Bool) : ∀ {M j}, j + 1 < nIt f M → f j = true
  | 0, _, h => absurd h (by simp [nIt])
  | M + 1, j, h => by
    unfold nIt at h
    split at h
    · rename_i ha
      exact List.all_eq_true.mp ha j (List.mem_range.mpr (by omega))
    · exact nIt_cont f h

theorem nIt_stop (f : Nat → Bool) : ∀ {M k}, k + 1 = nIt f M → k + 1 < M → f k = false
  | 0, _, h, _ => absurd h (by simp [nIt])
  | M + 1, k, h, hk => by
    unfold nIt at h
    split at h
    · omega
    · rename_i ha
      rcases (by omega : k + 1 < M ∨ k + 1 = M) with hk' | hk'
      · exact nIt_stop f h hk'
      · subst hk'
        -- `nIt f (k + 1) = k + 1`: either every iteration before `k` continued, or not.
        cases e : f k with
        | false => rfl
        | true =>
          refine absurd ?_ ha
          rw [List.all_eq_true]
          intro j hj
          rw [List.mem_range] at hj
          rcases (by omega : j < k ∨ j = k) with hj | rfl
          · have h2 := h
            unfold nIt at h2
            split at h2
            · rename_i hb; exact List.all_eq_true.mp hb j (List.mem_range.mpr hj)
            · have := nIt_le f k; omega
          · exact e

/-- Whether iteration `k < nIt f M` is followed by another one. -/
theorem nIt_next (f : Nat → Bool) {M k : Nat} (hk : k < nIt f M) :
    k + 1 < nIt f M ↔ f k = true ∧ k + 1 < M := by
  have hle := nIt_le f M
  constructor
  · intro h; exact ⟨nIt_cont f h, by omega⟩
  · rintro ⟨hf, hM⟩
    by_contra hn
    have := nIt_stop f (show k + 1 = nIt f M by omega) hM
    rw [hf] at this; cases this

/-- The iterations before one reached continued. -/
theorem nIt_before (f : Nat → Bool) {M k : Nat} (hk : k < nIt f M) : ∀ j < k, f j = true :=
  fun j hj => nIt_cont f (M := M) (by omega)

/-- Two loops that continue alike as long as either does run as many iterations. -/
theorem nIt_congr {f g : Nat → Bool} {N : Nat}
    (hfg : ∀ M < N, (∀ j < M, f j = true) → ∀ j < M, g j = true)
    (hgf : ∀ M < N, (∀ j < M, g j = true) → ∀ j < M, f j = true) : nIt f N = nIt g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    unfold nIt
    rw [ih (fun M hM => hfg M (by omega)) (fun M hM => hgf M (by omega))]
    have e : (List.range N).all f = (List.range N).all g := by
      cases e : (List.range N).all f with
      | true =>
        have := hfg N (by omega) fun j hj => List.all_eq_true.mp e j (List.mem_range.mpr hj)
        exact (List.all_eq_true.mpr fun j hj => this j (List.mem_range.mp hj)).symm
      | false =>
        cases e' : (List.range N).all g with
        | false => rfl
        | true =>
          have := hgf N (by omega) fun j hj => List.all_eq_true.mp e' j (List.mem_range.mpr hj)
          rw [List.all_eq_true.mpr fun j hj => this j (List.mem_range.mp hj)] at e
          cases e
    rw [e]

/-! ## The values -/

section
variable (p : Params) (sk mu rnd : List Byte)

/-- `ρ`. -/
abbrev rhoV : List Byte := sk.take 32
/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`. -/
abbrev rppV : List Byte := H ((sk.drop 32).take 32 ++ rnd ++ mu) 64
/-- `Â[i, j]`, within `maxBounds`. -/
abbrev Av : Nat → Nat → Poly := aF maxBounds.rejNTT (rhoV sk)

/-- The arguments of `signLoop`. -/
abbrev loopV (b : Bounds) (n κ : Nat) : Option (List Byte × List Poly × List (Vector Bool Spec.MlDsa.n)) :=
  signLoop p b (amat p (Av sk)) ((List.range p.ℓ).map (s1F p sk)) ((List.range p.k).map (s2F p sk))
    ((List.range p.k).map (t0F p sk)) mu (rppV sk mu rnd) n κ

abbrev iterV (b : Bounds) (κ : Nat) : Option (List Byte × Option (List Poly × List (Vector Bool Spec.MlDsa.n))) :=
  signIteration p b (amat p (Av sk)) ((List.range p.ℓ).map (s1F p sk)) ((List.range p.k).map (s2F p sk))
    ((List.range p.k).map (t0F p sk)) mu (rppV sk mu rnd) κ

/-- What the loop leaks. -/
abbrev leakV : List Nat :=
  signLeakLoopT p maxBounds (amat p (Av sk)) ((List.range p.ℓ).map (s1F p sk)) ((List.range p.k).map (s2F p sk))
    ((List.range p.k).map (t0F p sk)) mu (rppV sk mu rnd) maxBounds.sign 0

/-- `c̃` of the iteration with counter `κ`. -/
abbrev ctV (κ : Nat) : List Byte := ctF p (Av sk) mu (rppV sk mu rnd) κ
/-- `c = SampleInBall(c̃)`, within `maxBounds`. -/
abbrev cV (κ : Nat) : IPoly := (sampleInBall p.τ maxBounds.ball (ctV p sk mu rnd κ)).getD (Vector.replicate n 0)
/-- The validity checks pass. -/
abbrev passV (κ : Nat) : Prop :=
  passF p (Av sk) (s1F p sk) (s2F p sk) (t0F p sk) (rppV sk mu rnd) κ (cV p sk mu rnd κ)
abbrev zV (κ : Nat) : Nat → Poly := zF p (s1F p sk) (rppV sk mu rnd) κ (cV p sk mu rnd κ)
abbrev hV (κ : Nat) : Nat → Vector Bool n :=
  hF p (Av sk) (s2F p sk) (t0F p sk) (rppV sk mu rnd) κ (cV p sk mu rnd κ)
/-- The hint of the iteration with counter `κ`, as the list of its coefficients. -/
abbrev hbitsV (κ : Nat) : List Nat := ((List.range p.k).map (hV p sk mu rnd κ)).flatMap fun hi => hi.toList.map Bool.toNat

/-- The `t` iterations from counter 0 are rejected within `maxBounds`. -/
abbrev RejV (t : Nat) : Prop :=
  Rej p (amat p (Av sk)) ((List.range p.ℓ).map (s1F p sk)) ((List.range p.k).map (s2F p sk))
    ((List.range p.k).map (t0F p sk)) mu (rppV sk mu rnd) maxBounds 0 t

end

/-- An implementation's `SampleInBall` on `(τ, c̃)` succeeds exactly when
`ballF τ c̃`, and then within `maxBounds`. -/
def BallF (ballF : Nat → List Byte → Bool) : Prop :=
  ∀ τ B, ballF τ B = true → (sampleInBall τ maxBounds.ball B).isSome

section
variable (p : Params) (sk mu rnd : List Byte) (ballF : Nat → List Byte → Bool)

/-- Iteration `t` continues the loop: its `SampleInBall` succeeded and its checks failed. -/
def contV (t : Nat) : Bool := ballF p.τ (ctV p sk mu rnd (p.ℓ * t)) && !decide (passV p sk mu rnd (p.ℓ * t))

/-- The number of iterations the implementation runs. -/
abbrev itV : Nat := nIt (contV p sk mu rnd ballF) 814

end

/-! ## The iterations -/

section
variable {p : Params} {sk mu rnd : List Byte} {κ : Nat}

theorem cV_eq (h : (sampleInBall p.τ maxBounds.ball (ctV p sk mu rnd κ)).isSome) :
    sampleInBall p.τ maxBounds.ball (ctV p sk mu rnd κ) = some (cV p sk mu rnd κ) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  simp only [cV, hc, Option.getD_some]

theorem iterV_eq (hp : ParamsOk p) (b : Bounds) :
    iterV p sk mu rnd b κ = (sampleInBall p.τ b.ball (ctV p sk mu rnd κ)).map fun c =>
      (ctV p sk mu rnd κ, if passF p (Av sk) (s1F p sk) (s2F p sk) (t0F p sk) (rppV sk mu rnd) κ c then
        some ((List.range p.ℓ).map (zF p (s1F p sk) (rppV sk mu rnd) κ c),
          (List.range p.k).map (hF p (Av sk) (s2F p sk) (t0F p sk) (rppV sk mu rnd) κ c)) else none) :=
  signIteration_eqF hp b _ _ _ _ _ _ κ

theorem iterV_rej (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (ctV p sk mu rnd κ)).isSome)
    (hf : ¬ passV p sk mu rnd κ) : iterV p sk mu rnd maxBounds κ = some (ctV p sk mu rnd κ, none) := by
  rw [iterV_eq hp, cV_eq h, Option.map_some, ifn hf]

theorem iterV_pass (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (ctV p sk mu rnd κ)).isSome)
    (hf : passV p sk mu rnd κ) : iterV p sk mu rnd maxBounds κ =
      some (ctV p sk mu rnd κ, some ((List.range p.ℓ).map (zV p sk mu rnd κ), (List.range p.k).map (hV p sk mu rnd κ))) := by
  rw [iterV_eq hp, cV_eq h, Option.map_some, ifp hf]

theorem iterV_none (h : sampleInBall p.τ minBounds.ball (ctV p sk mu rnd κ) = none) :
    iterV p sk mu rnd minBounds κ = none := by
  rw [iterV, signIteration_eq, signCommit_eq, h]; rfl

variable {ballF : Nat → List Byte → Bool}

/-- Iterations that continued were rejected within `maxBounds`. -/
theorem rejV_of (hp : ParamsOk p) (hb : BallF ballF) {t : Nat}
    (h : ∀ j < t, contV p sk mu rnd ballF j = true) : RejV p sk mu rnd t := by
  intro j hj
  have hc := h j hj
  simp only [contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
  exact ⟨_, by rw [Nat.zero_add]; exact iterV_rej hp (hb _ _ hc.1) hc.2⟩

theorem loopV_pass (hp : ParamsOk p) (hb : BallF ballF) {t : Nat} (ht : t < maxBounds.sign)
    (h : ∀ j < t, contV p sk mu rnd ballF j = true) (hs : ballF p.τ (ctV p sk mu rnd (p.ℓ * t)) = true)
    (hpass : passV p sk mu rnd (p.ℓ * t)) :
    loopV p sk mu rnd maxBounds maxBounds.sign 0 =
      some (ctV p sk mu rnd (p.ℓ * t), (List.range p.ℓ).map (zV p sk mu rnd (p.ℓ * t)),
        (List.range p.k).map (hV p sk mu rnd (p.ℓ * t))) :=
  signLoop_pass _ _ _ _ _ _ _ (rejV_of hp hb h) ht (iterV_pass hp (hb _ _ hs) hpass)

theorem loopV_none_ball (hp : ParamsOk p) (hb : BallF ballF) {t : Nat}
    (h : ∀ j < t, contV p sk mu rnd ballF j = true)
    (hn : sampleInBall p.τ minBounds.ball (ctV p sk mu rnd (p.ℓ * t)) = none) :
    loopV p sk mu rnd minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) (rejV_of hp hb h)
    (.inr (by rw [Nat.zero_add]; exact iterV_none hn))

theorem loopV_none_exh (hp : ParamsOk p) (hb : BallF ballF) (h : ∀ j < 814, contV p sk mu rnd ballF j = true) :
    loopV p sk mu rnd minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) (rejV_of hp hb h) (.inl (by decide))

end

/-! ## What two runs leak -/

section
variable {p : Params} {sk mu rnd sk' mu' rnd' : List Byte}

theorem signLeakT_take (hl : 32 ≤ sk.length) : (signLeakT p sk mu rnd).take 32 = leakBytes (sk.take 32) := by
  unfold signLeakT
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  have hρ : ρ = sk.take 32 := by rw [← skRho_eq p sk, e]
  dsimp only
  subst hρ
  have hlen : (leakBytes (sk.take 32)).length = 32 := by rw [leakBytes_length, List.length_take]; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

theorem rho_of_leak (hl : 32 ≤ sk.length) (hl' : 32 ≤ sk'.length)
    (h : signLeakT p sk mu rnd = signLeakT p sk' mu' rnd') : rhoV sk = rhoV sk' := by
  have := congrArg (List.take 32) h
  rw [signLeakT_take hl, signLeakT_take hl'] at this
  exact leakBytes_inj this

/-- Once `ExpandA` finishes, the loops of two runs whose `signLeakT` agree leak the same. -/
theorem leakV_of_leak (hl : 32 ≤ sk.length) (hl' : 32 ≤ sk'.length)
    (hA : expandA p maxBounds (rhoV sk) = some (amat p (Av sk)))
    (hA' : expandA p maxBounds (rhoV sk') = some (amat p (Av sk')))
    (h : signLeakT p sk mu rnd = signLeakT p sk' mu' rnd') : leakV p sk mu rnd = leakV p sk' mu' rnd' := by
  have hr := rho_of_leak hl hl' h
  have hr' : sk.take 32 = sk'.take 32 := hr
  rw [signLeakT_eq hA, signLeakT_eq hA', hr'] at h
  exact List.append_cancel_left h

variable {ballF : Nat → List Byte → Bool}

/-- What two runs whose loops leak the same agree on, at an iteration they both reach. -/
theorem leak_iter (hp : ParamsOk p) (hb : BallF ballF) (h : leakV p sk mu rnd = leakV p sk' mu' rnd') :
    ∀ {t : Nat}, t < maxBounds.sign → (∀ j < t, contV p sk mu rnd ballF j = true) →
      (∀ j < t, contV p sk' mu' rnd' ballF j = true) ∧
      signLeakLoopT p maxBounds (amat p (Av sk)) ((List.range p.ℓ).map (s1F p sk)) ((List.range p.k).map (s2F p sk))
          ((List.range p.k).map (t0F p sk)) mu (rppV sk mu rnd) (maxBounds.sign - t) (p.ℓ * t) =
        signLeakLoopT p maxBounds (amat p (Av sk')) ((List.range p.ℓ).map (s1F p sk'))
          ((List.range p.k).map (s2F p sk')) ((List.range p.k).map (t0F p sk')) mu' (rppV sk' mu' rnd')
          (maxBounds.sign - t) (p.ℓ * t)
  | 0, _, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), by simpa using h⟩
  | t + 1, ht, hc => by
    obtain ⟨hc', ih⟩ := leak_iter hp hb h (t := t) (by omega) fun j hj => hc j (by omega)
    rw [show maxBounds.sign - t = (maxBounds.sign - (t + 1)) + 1 by
      have : maxBounds.sign = 1000 := rfl; omega] at ih
    obtain ⟨_, hrej, _⟩ := leakT_step ih
    have c1 := hc t (by omega)
    simp only [contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at c1
    obtain ⟨hr', hnext⟩ := hrej ⟨_, iterV_rej hp (hb _ _ c1.1) c1.2⟩
    refine ⟨fun j hj => ?_, by rw [show p.ℓ * (t + 1) = p.ℓ * t + p.ℓ by rw [Nat.mul_succ]]; exact hnext⟩
    rcases (by omega : j < t ∨ j = t) with hj | rfl
    · exact hc' j hj
    · obtain ⟨ct, hct⟩ := hr'
      change iterV p sk' mu' rnd' maxBounds (p.ℓ * j) = some (ct, none) at hct
      have hct' := hct
      rw [iterV_eq hp] at hct'
      obtain ⟨c, hcs, hc2⟩ := Option.map_eq_some_iff.mp hct'
      simp only [Prod.mk.injEq] at hc2
      have hpass : ¬ passV p sk' mu' rnd' (p.ℓ * j) := by
        intro hq
        rw [iterV_pass hp (by rw [hcs]; rfl) hq] at hct
        cases (Prod.mk.inj (Option.some.inj hct)).2
      -- `ballF` agrees, as `c̃` does.
      have ect : ctV p sk mu rnd (p.ℓ * j) = ctV p sk' mu' rnd' (p.ℓ * j) := by
        have := (leakT_step ih).1
        simpa [signCommit_eq] using this
      simp only [contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨by rw [← ect]; exact c1.1, hpass⟩

/-- At an iteration both runs reach: the same `c̃`, the same outcome of
`SampleInBall`, and, if it succeeded, the same outcome of the checks, and
then the same hint. -/
theorem leak_at (hp : ParamsOk p) (hb : BallF ballF) (h : leakV p sk mu rnd = leakV p sk' mu' rnd') {t : Nat}
    (ht : t < maxBounds.sign) (hc : ∀ j < t, contV p sk mu rnd ballF j = true) :
    ctV p sk mu rnd (p.ℓ * t) = ctV p sk' mu' rnd' (p.ℓ * t) ∧
      (ballF p.τ (ctV p sk mu rnd (p.ℓ * t)) = true →
        (passV p sk mu rnd (p.ℓ * t) ↔ passV p sk' mu' rnd' (p.ℓ * t)) ∧
        (passV p sk mu rnd (p.ℓ * t) → hbitsV p sk mu rnd (p.ℓ * t) = hbitsV p sk' mu' rnd' (p.ℓ * t))) := by
  obtain ⟨_, ih⟩ := leak_iter hp hb h ht hc
  rw [show maxBounds.sign - t = (maxBounds.sign - (t + 1)) + 1 by
    have : maxBounds.sign = 1000 := rfl; omega] at ih
  obtain ⟨hct, _, htag⟩ := leakT_step ih
  change outTag (iterV p sk mu rnd maxBounds (p.ℓ * t)) = outTag (iterV p sk' mu' rnd' maxBounds (p.ℓ * t)) at htag
  have ect : ctV p sk mu rnd (p.ℓ * t) = ctV p sk' mu' rnd' (p.ℓ * t) := by simpa [signCommit_eq] using hct
  refine ⟨ect, fun hs => ?_⟩
  have hs' : ballF p.τ (ctV p sk' mu' rnd' (p.ℓ * t)) = true := by rw [← ect]; exact hs
  have i1 := hb _ _ hs
  have i2 := hb _ _ hs'
  by_cases q1 : passV p sk mu rnd (p.ℓ * t) <;> by_cases q2 : passV p sk' mu' rnd' (p.ℓ * t)
  · rw [iterV_pass hp i1 q1, iterV_pass hp i2 q2] at htag
    refine ⟨iff_of_true q1 q2, fun _ => ?_⟩
    simp only [outTag, List.cons.injEq, true_and] at htag
    exact htag
  · rw [iterV_pass hp i1 q1, iterV_rej hp i2 q2] at htag
    simp [outTag] at htag
  · rw [iterV_rej hp i1 q1, iterV_pass hp i2 q2] at htag
    simp [outTag] at htag
  · exact ⟨iff_of_false q1 q2, fun h => absurd h q1⟩

/-- Two runs that leak the same run the same number of iterations. -/
theorem itV_eq (hp : ParamsOk p) (hb : BallF ballF) (h : leakV p sk mu rnd = leakV p sk' mu' rnd') :
    itV p sk mu rnd ballF = itV p sk' mu' rnd' ballF :=
  nIt_congr (fun M hM ha => (leak_iter hp hb h (t := M) (by show M < 1000; omega) ha).1)
    (fun M hM ha => (leak_iter hp hb h.symm (t := M) (by show M < 1000; omega) ha).1)

end

end VG.Proof.MlDsa.Sign

import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.Sha3.Stream

/-!
# ML-DSA key generation: larger bounds give the same result

The XOF output a sampler draws within a larger bound extends the output within
a smaller one (`H_take`, `G_take`), so a sampler that finishes within a bound
finishes with the same result within any larger one (`rejNTTPoly_mono`,
`rejBoundedPoly_mono`), and so does `ML-DSA.KeyGen_internal`
(`keyGenInternal_mono`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa
open VG.Spec.Sha3 (squeeze)

theorem ifp {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifn {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-! ## The XOFs -/

theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : Spec.Sha3.State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d :=
  List.ext_getElem (by rw [List.length_take, Proof.Sha3.length_squeeze hr hr', Proof.Sha3.length_squeeze hr hr']; omega)
    fun i h₁ h₂ => by
      rw [List.getElem_take, Proof.Sha3.squeeze_getElem hr hr' _ (by rw [List.length_take] at h₁; omega),
        Proof.Sha3.squeeze_getElem hr hr' _ (by rw [Proof.Sha3.length_squeeze hr hr'] at h₂; exact h₂)]

theorem H_eq (s : List Byte) (d : Nat) :
    H s d = squeeze 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix s)) d := rfl

theorem G_eq (s : List Byte) (d : Nat) :
    G s d = squeeze 168 (Spec.Sha3.absorb 168 (Spec.Sha3.pad 168 Spec.Sha3.shakeSuffix s)) d := rfl

theorem H_length (s : List Byte) (d : Nat) : (H s d).length = d := by
  rw [H_eq]; exact Proof.Sha3.length_squeeze (by decide) (by decide) _ _

theorem G_length (s : List Byte) (d : Nat) : (G s d).length = d := by
  rw [G_eq]; exact Proof.Sha3.length_squeeze (by decide) (by decide) _ _

theorem H_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (H s d').take d = H s d := by
  rw [H_eq, H_eq]; exact squeeze_take (by decide) (by decide) _ h

theorem G_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (G s d').take d = G s d := by
  rw [G_eq, G_eq]; exact squeeze_take (by decide) (by decide) _ h

theorem H_append (s : List Byte) {d d' : Nat} (h : d ≤ d') : H s d' = H s d ++ (H s d').drop d := by
  rw [← H_take s h, List.take_append_drop]

theorem G_append (s : List Byte) {d d' : Nat} (h : d ≤ d') : G s d' = G s d ++ (G s d').drop d := by
  rw [← G_take s h, List.take_append_drop]

/-! ## The loops -/

theorem rejNTTLoop_done {a : List Zq} (h : n ≤ a.length) : ∀ l, rejNTTLoop a l = some a
  | _ :: _ :: _ :: _ => by rw [rejNTTLoop, ifp h]
  | [] => by rw [rejNTTLoop.eq_2 _ _ (by simp), ifp h]
  | [_] => by rw [rejNTTLoop.eq_2 _ _ (by simp), ifp h]
  | [_, _] => by rw [rejNTTLoop.eq_2 _ _ (by simp), ifp h]

theorem rejNTTLoop_append : ∀ (a : List Zq) (l l' : List Byte) {r : List Zq},
    rejNTTLoop a l = some r → rejNTTLoop a (l ++ l') = some r
  | a, s₀ :: s₁ :: s₂ :: out, l', r, h => by
    rw [rejNTTLoop] at h
    rw [List.cons_append, List.cons_append, List.cons_append, rejNTTLoop]
    split at h
    · rw [ifp ‹_›]; exact h
    · rw [ifn ‹_›]; exact rejNTTLoop_append _ out l' h
  | a, [], l', r, h | a, [_], l', r, h | a, [_, _], l', r, h => by
    rw [rejNTTLoop.eq_2 _ _ (by simp)] at h
    split at h
    · cases h; exact rejNTTLoop_done ‹_› _
    · cases h

theorem rejBoundedLoop_done {η : Nat} {a : List Int} (h : n ≤ a.length) : ∀ l, rejBoundedLoop η a l = some a
  | [] => by rw [rejBoundedLoop, ifp h]
  | _ :: _ => by rw [rejBoundedLoop, ifp h]

theorem rejBoundedLoop_append {η : Nat} : ∀ (a : List Int) (l l' : List Byte) {r : List Int},
    rejBoundedLoop η a l = some r → rejBoundedLoop η a (l ++ l') = some r
  | a, [], l', r, h => by
    rw [rejBoundedLoop] at h
    split at h
    · cases h; exact rejBoundedLoop_done ‹_› _
    · cases h
  | a, z :: out, l', r, h => by
    rw [rejBoundedLoop] at h
    rw [List.cons_append, rejBoundedLoop]
    split at h
    · rw [ifp ‹_›]; exact h
    · rw [ifn ‹_›]; exact rejBoundedLoop_append _ out l' h

/-! ## The samplers -/

theorem rejNTTPoly_mono {b b' : Nat} (h : b ≤ b') {ρ : List Byte} {x : Poly}
    (hx : rejNTTPoly b ρ = some x) : rejNTTPoly b' ρ = some x := by
  unfold rejNTTPoly at hx ⊢
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hx
  rw [G_append ρ h, rejNTTLoop_append _ _ _ ha]
  rfl

theorem rejBoundedPoly_mono {η b b' : Nat} (h : b ≤ b') {ρ : List Byte} {x : IPoly}
    (hx : rejBoundedPoly η b ρ = some x) : rejBoundedPoly η b' ρ = some x := by
  unfold rejBoundedPoly at hx ⊢
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hx
  rw [H_append ρ h, rejBoundedLoop_append _ _ _ ha]
  rfl

/-! ## Bounds -/

/-- `b` is at most `b'` on every loop. -/
structure Bounds.Le (b b' : Bounds) : Prop where
  sign : b.sign ≤ b'.sign
  rejBounded : b.rejBounded ≤ b'.rejBounded
  rejNTT : b.rejNTT ≤ b'.rejNTT
  ball : b.ball ≤ b'.ball

/-- The larger of two bounds on every loop. -/
def bmax (b b' : Bounds) : Bounds :=
  { sign := Nat.max b.sign b'.sign, rejBounded := Nat.max b.rejBounded b'.rejBounded,
    rejNTT := Nat.max b.rejNTT b'.rejNTT, ball := Nat.max b.ball b'.ball }

theorem Bounds.le_max_left (b b' : Bounds) : Bounds.Le b (bmax b b') :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩

theorem Bounds.le_max_right (b b' : Bounds) : Bounds.Le b' (bmax b b') :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-! ## `mapM` in `Option` -/

theorem mapM_some {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x (List.mem_cons_self ..), mapM_some fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem mapM_none {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∃ x ∈ l, f x = none) → l.mapM f = none
  | [], ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | x :: l, ⟨y, hy, hn⟩ => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hn]; rfl
    · cases e : f x with
      | none => rfl
      | some _ => rw [mapM_none ⟨y, hy, hn⟩]; rfl

theorem mapM_mono {α β : Type} {f g : α → Option β} (hfg : ∀ x y, f x = some y → g x = some y) :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → l.mapM g = some r
  | [], _, h => h
  | x :: l, r, h => by
    rw [List.mapM_cons] at h ⊢
    cases e : f x with
    | none => rw [e] at h; cases h
    | some y =>
      rw [e] at h
      cases e' : l.mapM f with
      | none => rw [e'] at h; cases h
      | some ys =>
        rw [e'] at h
        rw [hfg x y e, mapM_mono hfg e']
        exact h

/-! ## `ExpandA`, `ExpandS` and key generation -/

/-- The seed of `Â[r, s]`. -/
abbrev seedA (ρ : List Byte) (r s : Nat) : List Byte := ρ ++ integerToBytes s 1 ++ integerToBytes r 1

/-- The seed of entry `r` of `s₁ ‖ s₂`. -/
abbrev seedS (ρ' : List Byte) (r : Nat) : List Byte := ρ' ++ integerToBytes r 2

theorem expandA_mono {p : Params} {b b' : Bounds} (h : Bounds.Le b b') {ρ : List Byte} {x : List (List Poly)}
    (hx : expandA p b ρ = some x) : expandA p b' ρ = some x :=
  mapM_mono (fun _ _ hr => mapM_mono (fun _ _ hs => rejNTTPoly_mono h.rejNTT hs) hr) hx

theorem expandS_eq (p : Params) (b : Bounds) (ρ : List Byte) :
    expandS p b ρ = ((List.range p.ℓ).mapM fun r => rejBoundedPoly p.η b.rejBounded (seedS ρ r)).bind
      fun s₁ => ((List.range p.k).mapM fun r => rejBoundedPoly p.η b.rejBounded (seedS ρ (r + p.ℓ))).map
        fun s₂ => (s₁, s₂) := by
  unfold expandS
  cases (List.range p.ℓ).mapM fun r => rejBoundedPoly p.η b.rejBounded (seedS ρ r) with
  | none => rfl
  | some s₁ =>
    cases (List.range p.k).mapM fun r => rejBoundedPoly p.η b.rejBounded (seedS ρ (r + p.ℓ)) with
    | none => rfl
    | some s₂ => rfl

theorem expandS_mono {p : Params} {b b' : Bounds} (h : Bounds.Le b b') {ρ : List Byte} {x : List IPoly × List IPoly}
    (hx : expandS p b ρ = some x) : expandS p b' ρ = some x := by
  rw [expandS_eq] at hx ⊢
  obtain ⟨s₁, h₁, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨s₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hx
  rw [mapM_mono (fun _ _ hs => rejBoundedPoly_mono h.rejBounded hs) h₁, Option.bind_some,
    mapM_mono (fun _ _ hs => rejBoundedPoly_mono h.rejBounded hs) h₂]
  rfl

/-- `ExpandA` when every entry is sampled. -/
theorem expandA_some {p : Params} {b : Bounds} {ρ : List Byte} {A : Nat → Nat → Poly}
    (h : ∀ r < p.k, ∀ s < p.ℓ, rejNTTPoly b.rejNTT (seedA ρ r s) = some (A r s)) :
    expandA p b ρ = some ((List.range p.k).map fun r => (List.range p.ℓ).map fun s => A r s) :=
  mapM_some fun r hr => mapM_some fun s hs => h r (List.mem_range.mp hr) s (List.mem_range.mp hs)

theorem expandA_none {p : Params} {b : Bounds} {ρ : List Byte}
    (h : ∃ r < p.k, ∃ s < p.ℓ, rejNTTPoly b.rejNTT (seedA ρ r s) = none) : expandA p b ρ = none := by
  obtain ⟨r, hr, s, hs, hn⟩ := h
  exact mapM_none ⟨r, List.mem_range.mpr hr, mapM_none ⟨s, List.mem_range.mpr hs, hn⟩⟩

/-- `ExpandS` when every entry is sampled. -/
theorem expandS_some {p : Params} {b : Bounds} {ρ' : List Byte} {S : Nat → IPoly}
    (h : ∀ r < p.ℓ + p.k, rejBoundedPoly p.η b.rejBounded (seedS ρ' r) = some (S r)) :
    expandS p b ρ' = some ((List.range p.ℓ).map S, (List.range p.k).map fun r => S (r + p.ℓ)) := by
  rw [expandS_eq, mapM_some (g := S) fun r hr => h r (by have := List.mem_range.mp hr; omega),
    Option.bind_some, mapM_some (g := fun r => S (r + p.ℓ)) fun r hr => h (r + p.ℓ) (by have := List.mem_range.mp hr; omega)]
  rfl

theorem expandS_none {p : Params} {b : Bounds} {ρ' : List Byte}
    (h : ∃ r < p.ℓ + p.k, rejBoundedPoly p.η b.rejBounded (seedS ρ' r) = none) : expandS p b ρ' = none := by
  obtain ⟨r, hr, hn⟩ := h
  rw [expandS_eq]
  by_cases hl : r < p.ℓ
  · rw [mapM_none ⟨r, List.mem_range.mpr hl, hn⟩]; rfl
  · rw [mapM_none (l := List.range p.k) ⟨r - p.ℓ, List.mem_range.mpr (by omega), by rw [Nat.sub_add_cancel (by omega)]; exact hn⟩]
    cases (List.mapM _ _ : Option (List IPoly)) <;> rfl

/-- `ML-DSA.KeyGen_internal` after `ExpandA` and `ExpandS`: lines 5–10 of Algorithm 6. -/
def kgRest (p : Params) (ρ K : List Byte) (Â : List (List Poly)) (s₁ s₂ : List IPoly) : List Byte × List Byte :=
  let ŝ₁ := s₁.map fun s => ntt (toRq s)
  let t := addVec ((matrixVectorNTT Â ŝ₁).map nttInv) (s₂.map toRq)
  let t₁ := t.map fun ti => ti.map fun c => (power2Round c).1.toNat
  let t₀ := t.map fun ti => ti.map fun c => (power2Round c).2
  let pk := pkEncode ρ t₁
  (pk, skEncode p ρ K (H pk 64) s₁ s₂ t₀)

theorem keyGenInternal_eq (p : Params) (b : Bounds) (ξ : List Byte) :
    keyGenInternal p b ξ =
      (expandA p b (keyGenSeeds p ξ).1).bind fun Â => (expandS p b (keyGenSeeds p ξ).2.1).map fun s =>
        kgRest p (keyGenSeeds p ξ).1 (keyGenSeeds p ξ).2.2 Â s.1 s.2 := by
  unfold keyGenInternal keyGenSeeds
  dsimp only
  cases expandA p b (List.take 32 (H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128)) with
  | none => rfl
  | some Â =>
    cases expandS p b (List.take 64 (List.drop 32 (H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128))) with
    | none => rfl
    | some s => rfl

theorem keyGenInternal_mono {p : Params} {b b' : Bounds} (h : Bounds.Le b b') {ξ : List Byte}
    {x : List Byte × List Byte} (hx : keyGenInternal p b ξ = some x) : keyGenInternal p b' ξ = some x := by
  rw [keyGenInternal_eq] at hx ⊢
  obtain ⟨Â, hA, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨s, hS, rfl⟩ := Option.map_eq_some_iff.mp hx
  rw [expandA_mono h hA, Option.bind_some, expandS_mono h hS]
  rfl

end VG.Proof.MlDsa.KeyGen

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

/-- Key generation fails within the least bounds if an entry of `Â` does. -/
theorem keyGenInternal_none_A {p : Params} {ξ : List Byte} {r s : Nat} (hr : r < p.k) (hs : s < p.ℓ)
    (h : rejNTTPoly minBounds.rejNTT (seedA (keyGenSeeds p ξ).1 r s) = none) : keyGenInternal p minBounds ξ = none := by
  rw [keyGenInternal_eq, expandA_none ⟨r, hr, s, hs, h⟩]; rfl

/-- Key generation fails within the least bounds if an entry of `s₁ ‖ s₂` does. -/
theorem keyGenInternal_none_S {p : Params} {ξ : List Byte} {r : Nat} (hr : r < p.ℓ + p.k)
    (h : rejBoundedPoly p.η minBounds.rejBounded (seedS (keyGenSeeds p ξ).2.1 r) = none) :
    keyGenInternal p minBounds ξ = none := by
  rw [keyGenInternal_eq, expandS_none ⟨r, hr, h⟩]
  cases expandA p minBounds (keyGenSeeds p ξ).1 <;> rfl

end VG.Proof.MlDsa.KeyGen

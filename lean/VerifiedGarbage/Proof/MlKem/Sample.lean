import VerifiedGarbage.Proof.MlKem.Hash
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Spec.MlKem.Contract

/-!
# ML-KEM: SampleNTT as a loop, and bounds on its iterations

Untrusted: everything here is checked by Lean. `SampleNTT` (Algorithm 7) as
the loop an implementation runs over the 3-byte chunks of the XOF output
(`xofByte`, `Hash.lean`): `sampleAfter a out t` is the list of coefficients
accepted after the first `t` chunks, which stops growing once it has 256
(`sampleStepCap`). An implementation that bounds the loop by `iters`
iterations and stops after `t ≤ iters` chunks with 256 coefficients
computes `sampleNTT iters B` (`sampleNTT_of_full`); one that reaches the
bound with fewer has `sampleNTT iters B = none` (`sampleNTT_none`).

A bigger bound gives the same result once the result is `some`
(`sampleNTT_mono`), and so do the algorithms built on `SampleNTT`
(`kpkeKeyGen_mono`, `kpkeEncrypt_mono`, `keyGenInternal_mono`,
`encapsInternal_mono`, `decapsInternal_mono`), and `Outcome` holds for an
implementation that bounds each `SampleNTT` by `minIterations`
(`outcome_of_min`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## One iteration -/

/-- Lines 5–15 of Algorithm 7 on the chunk `C = (c₀, c₁, c₂)`, from the
coefficients `a` sampled so far. -/
def sampleStep (a : List Zq) (c₀ c₁ c₂ : Byte) : List Zq :=
  let d₁ := c₀.toNat + 256 * (c₁.toNat % 16)
  let d₂ := c₁.toNat / 16 + 16 * c₂.toNat
  let a := if d₁ < q then a ++ [ofNat d₁] else a
  if d₂ < q ∧ a.length < n then a ++ [ofNat d₂] else a

/-- An iteration of the loop, which does nothing once there are 256
coefficients (the loop has ended). -/
def sampleStepCap (a : List Zq) (c₀ c₁ c₂ : Byte) : List Zq :=
  if a.length = n then a else sampleStep a c₀ c₁ c₂

/-- The coefficients sampled from `a` on after the first `t` chunks of the
bytes `out`, the loop stopping at 256 coefficients. -/
def sampleAfter (a : List Zq) (out : Nat → Byte) : Nat → List Zq
  | 0 => a
  | t + 1 => sampleStepCap (sampleAfter a out t) (out (3 * t)) (out (3 * t + 1)) (out (3 * t + 2))

/-- The element of `T_q` whose coefficients are the first 256 of `a`. -/
def toPoly (a : List Zq) : Poly := Vector.ofFn fun i => a.getD i.val 0

theorem sampleAfter_zero (a : List Zq) (out : Nat → Byte) : sampleAfter a out 0 = a := rfl

theorem sampleAfter_succ (a : List Zq) (out : Nat → Byte) (t : Nat) :
    sampleAfter a out (t + 1) =
      sampleStepCap (sampleAfter a out t) (out (3 * t)) (out (3 * t + 1)) (out (3 * t + 2)) := rfl

theorem sampleStep_length (a : List Zq) (c₀ c₁ c₂ : Byte) (ha : a.length < n) :
    (sampleStep a c₀ c₁ c₂).length ≤ n := by
  simp only [sampleStep]
  split <;> split <;> simp_all <;> omega

theorem sampleStepCap_length {a : List Zq} (ha : a.length ≤ n) (c₀ c₁ c₂ : Byte) :
    (sampleStepCap a c₀ c₁ c₂).length ≤ n := by
  unfold sampleStepCap
  split
  · exact ha
  · exact sampleStep_length a c₀ c₁ c₂ (by omega)

theorem sampleStepCap_full {a : List Zq} (ha : a.length = n) (c₀ c₁ c₂ : Byte) :
    sampleStepCap a c₀ c₁ c₂ = a := by
  unfold sampleStepCap; rw [ite_eq_left ha]

/-- An iteration keeps the coefficients sampled before it. -/
theorem sampleStepCap_prefix (a : List Zq) (c₀ c₁ c₂ : Byte) : a <+: sampleStepCap a c₀ c₁ c₂ := by
  unfold sampleStepCap sampleStep
  split
  · exact List.prefix_refl a
  · dsimp only
    split <;> split
    all_goals first
      | exact List.prefix_refl a
      | exact List.prefix_append a _
      | exact (List.prefix_append a _).trans (List.prefix_append _ _)

theorem sampleAfter_length_le {a : List Zq} (ha : a.length ≤ n) (out : Nat → Byte) :
    ∀ t, (sampleAfter a out t).length ≤ n
  | 0 => ha
  | t + 1 => sampleStepCap_length (sampleAfter_length_le ha out t) _ _ _

/-- Once there are 256 coefficients, they stay. -/
theorem sampleAfter_full {a : List Zq} {out : Nat → Byte} {t : Nat} (h : (sampleAfter a out t).length = n) :
    ∀ t', t ≤ t' → sampleAfter a out t' = sampleAfter a out t := by
  intro t' ht
  have : ∀ k, sampleAfter a out (t + k) = sampleAfter a out t := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← Nat.add_assoc, sampleAfter_succ, ih, sampleStepCap_full h]
  rw [← this (t' - t), Nat.add_sub_cancel' ht]

/-- The coefficients sampled only depend on the bytes of the chunks read. -/
theorem sampleAfter_congr (a : List Zq) {out out' : Nat → Byte} :
    ∀ {t}, (∀ p < 3 * t, out p = out' p) → sampleAfter a out t = sampleAfter a out' t
  | 0, _ => rfl
  | t + 1, h => by
    rw [sampleAfter_succ, sampleAfter_succ, sampleAfter_congr a fun p hp => h p (by omega),
      h _ (by omega), h _ (by omega), h _ (by omega)]

/-- The first chunk, then the others. -/
theorem sampleAfter_succ' (a : List Zq) (out : Nat → Byte) :
    ∀ t, sampleAfter a out (t + 1) =
      sampleAfter (sampleStepCap a (out 0) (out 1) (out 2)) (fun p => out (p + 3)) t
  | 0 => rfl
  | t + 1 => by
    rw [sampleAfter_succ, sampleAfter_succ' a out t, sampleAfter_succ]
    congr 2 <;> congr 1 <;> omega

/-! ## The loop of the standard -/

/-- `sampleLoop` after it stops: the coefficients if there are 256. -/
private theorem sampleLoop_eq_after :
    ∀ (L : List Byte) (a : List Zq), a.length ≤ n →
      sampleLoop a L =
        if (sampleAfter a (fun p => L.getD p 0) (L.length / 3)).length = n
        then some (sampleAfter a (fun p => L.getD p 0) (L.length / 3)) else none
  | c₀ :: c₁ :: c₂ :: L, a, ha => by
    rw [sampleLoop]
    by_cases h : a.length = n
    · rw [ite_eq_left h, sampleAfter_full (t := 0) h _ (Nat.zero_le _), sampleAfter_zero, ite_eq_left h]
    · rw [ite_eq_right h]
      have hs : (c₀ :: c₁ :: c₂ :: L).length / 3 = L.length / 3 + 1 := by simp; omega
      have hf : (fun p => (c₀ :: c₁ :: c₂ :: L).getD (p + 3) 0) = fun p => L.getD p 0 := by
        funext p; simp only [List.getD_cons_succ]
      rw [hs, sampleAfter_succ', hf]
      simp only [List.getD_cons_zero, List.getD_cons_succ, sampleStepCap, ite_eq_right h]
      exact sampleLoop_eq_after L _ (sampleStep_length a c₀ c₁ c₂ (by omega))
  | [], a, _ => by
    rw [show ([] : List Byte).length / 3 = 0 by simp, sampleAfter_zero]; unfold sampleLoop; rfl
  | [x], a, _ => by
    rw [show [x].length / 3 = 0 by simp, sampleAfter_zero]; unfold sampleLoop; rfl
  | [x, y], a, _ => by
    rw [show [x, y].length / 3 = 0 by simp, sampleAfter_zero]; unfold sampleLoop; rfl

/-- `SampleNTT` with its loop bounded by `iters` iterations, as the
coefficients sampled after `iters` chunks of the XOF output. -/
theorem sampleNTT_eq (iters : Nat) (B : List Byte) :
    sampleNTT iters B =
      if (sampleAfter [] (xofByte B) iters).length = n
      then some (toPoly (sampleAfter [] (xofByte B) iters)) else none := by
  rw [sampleNTT, sampleLoop_eq_after _ [] (Nat.zero_le _), xof_length,
    show 3 * iters / 3 = iters by omega,
    sampleAfter_congr [] (out' := xofByte B) fun p hp => xof_getD B hp]
  split <;> rfl

/-- An implementation that has 256 coefficients after `t ≤ iters` chunks
computes `SampleNTT` bounded by `iters`. -/
theorem sampleNTT_of_full {iters t : Nat} {B : List Byte} (ht : t ≤ iters)
    (h : (sampleAfter [] (xofByte B) t).length = n) :
    sampleNTT iters B = some (toPoly (sampleAfter [] (xofByte B) t)) := by
  rw [sampleNTT_eq, sampleAfter_full h _ ht, ite_eq_left h]

/-- An implementation that has fewer than 256 coefficients after `iters`
chunks: `SampleNTT` bounded by `iters` fails. -/
theorem sampleNTT_none {iters : Nat} {B : List Byte} (h : (sampleAfter [] (xofByte B) iters).length ≠ n) :
    sampleNTT iters B = none := by
  rw [sampleNTT_eq, ite_eq_right h]

/-- A bigger bound on the iterations gives the same result. -/
theorem sampleNTT_mono {iters iters' : Nat} {B : List Byte} {a : Poly} (h : sampleNTT iters B = some a)
    (hi : iters ≤ iters') : sampleNTT iters' B = some a := by
  rw [sampleNTT_eq] at h
  split at h
  · rename_i hf
    rw [sampleNTT_of_full hi hf, h]
  · cases h

/-! ## The algorithms that sample -/

/-- `f` with a bound on the iterations of `SampleNTT` gives the same result
with any bigger bound, once it is `some`. -/
def Mono {α : Type} (f : Nat → Option α) : Prop :=
  ∀ ⦃iters iters' : Nat⦄ ⦃a : α⦄, f iters = some a → iters ≤ iters' → f iters' = some a

theorem Mono.bind {α β : Type} {f : Nat → Option α} (hf : Mono f) (g : α → Option β) :
    Mono fun iters => (f iters).bind g := by
  intro i i' b h hi
  dsimp only at h ⊢
  cases hx : f i with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; rw [hf hx hi]; exact h

theorem Mono.map {α β : Type} {f : Nat → Option α} (hf : Mono f) (g : α → β) :
    Mono fun iters => (f iters).map g := by
  intro i i' b h hi
  dsimp only at h ⊢
  cases hx : f i with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; rw [hf hx hi]; exact h

theorem mapM_mono {α β : Type} {f : α → Nat → Option β} (hf : ∀ x, Mono (f x)) :
    ∀ L : List α, Mono fun iters => L.mapM fun x => f x iters
  | [] => fun _ _ _ h _ => h
  | x :: L => by
    intro i i' b h hi
    simp only [List.mapM_cons] at h ⊢
    cases hx : f x i with
    | none => rw [hx] at h; cases h
    | some y =>
      rw [hx] at h
      cases hL : L.mapM (fun x => f x i) with
      | none => rw [hL] at h; cases h
      | some ys =>
        rw [hL] at h
        simp only [hf x hx hi, mapM_mono hf L hL hi]
        exact h

theorem sampleNTT_mono' (B : List Byte) : Mono fun iters => sampleNTT iters B :=
  fun _ _ _ h hi => sampleNTT_mono h hi

theorem sampleMatrix_mono (k : Nat) (ρ : List Byte) : Mono fun iters => sampleMatrix k iters ρ :=
  mapM_mono (fun _ => mapM_mono (fun _ => sampleNTT_mono' _) _) _

theorem kpkeKeyGen_mono (p : Params) (d : List Byte) : Mono fun iters => kpkeKeyGen p iters d := by
  simp only [kpkeKeyGen]
  exact (sampleMatrix_mono _ _).bind _

theorem kpkeEncrypt_mono (p : Params) (ek m r : List Byte) :
    Mono fun iters => kpkeEncrypt p iters ek m r := by
  simp only [kpkeEncrypt]
  exact (sampleMatrix_mono _ _).bind _

theorem keyGenInternal_mono (p : Params) (d z : List Byte) :
    Mono fun iters => keyGenInternal p iters d z := by
  simp only [keyGenInternal]
  exact (kpkeKeyGen_mono p d).bind _

theorem encapsInternal_mono (p : Params) (ek m : List Byte) :
    Mono fun iters => encapsInternal p iters ek m := by
  simp only [encapsInternal]
  exact (kpkeEncrypt_mono p ek m _).bind _

theorem decapsInternal_mono (p : Params) (dk c : List Byte) :
    Mono fun iters => decapsInternal p iters dk c := by
  simp only [decapsInternal]
  exact (kpkeEncrypt_mono p _ _ _).bind _

/-- The return value of an implementation that bounds each `SampleNTT` by
`minIterations` iterations: 1 if the algorithm so bounded succeeds, and 0
if not. -/
theorem outcome_of_min {α : Type} {f : Nat → Option α} {r : BitVec 32} {out : α}
    (h : (r = 1 ∧ f minIterations = some out) ∨ (r = 0 ∧ f minIterations = none)) :
    Outcome f r out := by
  rcases h with ⟨hr, hf⟩ | ⟨hr, hf⟩
  · exact .inl ⟨hr, minIterations, hf⟩
  · exact .inr ⟨hr, hf⟩

end VG.Proof.MlKem

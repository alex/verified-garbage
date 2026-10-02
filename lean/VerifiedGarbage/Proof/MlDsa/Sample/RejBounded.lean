import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.MlDsa.Sample.Mem

/-!
# ML-DSA: `RejBoundedPoly` a byte at a time

An implementation that runs the loop of `RejBoundedPoly` (Algorithm 31) over a
fixed number of bytes of XOF output, doing nothing once it has 256
coefficients, samples `rbFold η [] out` (`rbStep` is one iteration, `hbTry` a
half-byte), as elements of `ℤ_q`. It computes `RejBoundedPoly` if that has 256
coefficients (`rejBounded_some`), and otherwise so does no shorter output
(`rejBounded_none`).

How many coefficients it has sampled depends only on which half-bytes it
accepted (`rbFold_length_congr`), which is what the contract lets it leak
(`rejBoundedLeak`, `leak_hbOks`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- The half-byte `b`, tried: its coefficient appended if it is accepted. -/
def hbTry (η : Nat) (a : List Zq) (b : Nat) : List Zq :=
  match coeffFromHalfByte η b with
  | some c => a ++ [ofInt c]
  | none => a

/-- One iteration of the loop of `RejBoundedPoly` (lines 5–15 of
Algorithm 31), which does nothing once there are 256 coefficients. -/
def rbStep (η : Nat) (a : List Zq) (z : Byte) : List Zq :=
  if a.length < n then
    (if (hbTry η a (z.toNat % 16)).length < n then hbTry η (hbTry η a (z.toNat % 16)) (z.toNat / 16)
      else hbTry η a (z.toNat % 16))
  else a

/-- The coefficients after the loop over the bytes of `L`. -/
def rbFold (η : Nat) : List Zq → List Byte → List Zq
  | a, z :: L => rbFold η (rbStep η a z) L
  | a, [] => a

theorem hbTry_length (η : Nat) (a : List Zq) (b : Nat) :
    (hbTry η a b).length = a.length + halfByteOk η b := by
  unfold hbTry halfByteOk
  split <;> rename_i h <;> simp [h]

theorem halfByteOk_le (η b : Nat) : halfByteOk η b ≤ 1 := by
  unfold halfByteOk; split <;> omega

theorem rbStep_length (η : Nat) (a : List Zq) (z : Byte) :
    (rbStep η a z).length =
      if a.length < n then
        (if a.length + halfByteOk η (z.toNat % 16) < n then
          a.length + halfByteOk η (z.toNat % 16) + halfByteOk η (z.toNat / 16)
        else a.length + halfByteOk η (z.toNat % 16))
      else a.length := by
  unfold rbStep
  simp only [hbTry_length]
  split
  · split <;> simp only [hbTry_length]
  · rfl

theorem rbStep_length_le {η : Nat} {a : List Zq} (ha : a.length ≤ n) (z : Byte) : (rbStep η a z).length ≤ n := by
  rw [rbStep_length]
  have := halfByteOk_le η (z.toNat % 16)
  have := halfByteOk_le η (z.toNat / 16)
  split
  · split <;> omega
  · exact ha

theorem rbStep_full {η : Nat} {a : List Zq} (ha : a.length = n) (z : Byte) : rbStep η a z = a := by
  unfold rbStep; rw [ifF (by omega)]

theorem rbFold_full {η : Nat} {a : List Zq} (ha : a.length = n) : ∀ L, rbFold η a L = a
  | z :: L => by rw [rbFold, rbStep_full ha, rbFold_full ha L]
  | [] => rfl

theorem rbFold_length_le {η : Nat} {a : List Zq} (ha : a.length ≤ n) : ∀ L, (rbFold η a L).length ≤ n
  | z :: L => by rw [rbFold]; exact rbFold_length_le (rbStep_length_le ha z) L
  | [] => ha

theorem rbFold_append (η : Nat) (a : List Zq) : ∀ L₁ L₂ : List Byte,
    rbFold η a (L₁ ++ L₂) = rbFold η (rbFold η a L₁) L₂
  | [], _ => rfl
  | z :: L₁, L₂ => by simp only [List.cons_append, rbFold]; exact rbFold_append η _ L₁ L₂

theorem rbFold_snoc (η : Nat) (a : List Zq) (L : List Byte) (z : Byte) :
    rbFold η a (L ++ [z]) = rbStep η (rbFold η a L) z := by
  rw [rbFold_append]; rfl

/-! ## The loop of the standard -/

/-- The half-byte `b`, tried as the standard does, on integers. -/
def hbTryI (η : Nat) (a : List Int) (b : Nat) : List Int :=
  match coeffFromHalfByte η b with
  | some c => a ++ [c]
  | none => a

theorem hbTryI_map (η : Nat) (a : List Int) (b : Nat) :
    (hbTryI η a b).map ofInt = hbTry η (a.map ofInt) b := by
  unfold hbTryI hbTry; split <;> simp

theorem rejBoundedLoop_step (η : Nat) {a : List Int} (ha : a.length < n) (z : Byte) (L : List Byte) :
    rejBoundedLoop η a (z :: L) =
      rejBoundedLoop η (if (hbTryI η a (z.toNat % 16)).length < n then
        hbTryI η (hbTryI η a (z.toNat % 16)) (z.toNat / 16) else hbTryI η a (z.toNat % 16)) L := by
  rw [rejBoundedLoop, ifF (by omega)]
  dsimp only
  congr 1
  unfold hbTryI
  cases coeffFromHalfByte η (z.toNat / 16) with
  | none => exact (ite_self _).symm
  | some c => rfl

/-- The loop, as `rbFold` on the coefficients as elements of `ℤ_q`: it
succeeds when that has 256 coefficients. -/
theorem rejBoundedLoop_map (η : Nat) {a : List Int} (ha : a.length ≤ n) :
    ∀ L, (rejBoundedLoop η a L).map (·.map ofInt) =
      if (rbFold η (a.map ofInt) L).length = n then some (rbFold η (a.map ofInt) L) else none
  | z :: L => by
    by_cases h : a.length ≥ n
    · rw [rejBoundedLoop, ifT h, rbFold, rbStep_full (by simp; omega), rbFold_full (by simp; omega),
        ifT (by simp; omega)]
      rfl
    · rw [rejBoundedLoop_step η (by omega)]
      have e1 := hbTryI_map η a (z.toNat % 16)
      have l1 : (hbTryI η a (z.toNat % 16)).length = (hbTry η (a.map ofInt) (z.toNat % 16)).length := by
        rw [← e1, List.length_map]
      have l1' : (hbTryI η a (z.toNat % 16)).length ≤ n := by
        rw [l1, hbTry_length, List.length_map]; have := halfByteOk_le η (z.toNat % 16); omega
      have e2 : (if (hbTryI η a (z.toNat % 16)).length < n then
            hbTryI η (hbTryI η a (z.toNat % 16)) (z.toNat / 16) else hbTryI η a (z.toNat % 16)).map ofInt =
          rbStep η (a.map ofInt) z := by
        have hlen : (List.map ofInt a).length < n := by rw [List.length_map]; omega
        by_cases hl : (hbTryI η a (z.toNat % 16)).length < n
        · have hl' : (hbTry η (a.map ofInt) (z.toNat % 16)).length < n := by rw [← l1]; exact hl
          rw [ifT hl, rbStep, ifT hlen, ifT hl', hbTryI_map, e1]
        · have hl' : ¬ (hbTry η (a.map ofInt) (z.toNat % 16)).length < n := by rw [← l1]; exact hl
          rw [ifF hl, rbStep, ifT hlen, ifF hl', e1]
      have l2 : (if (hbTryI η a (z.toNat % 16)).length < n then
            hbTryI η (hbTryI η a (z.toNat % 16)) (z.toNat / 16) else hbTryI η a (z.toNat % 16)).length ≤ n := by
        have := congrArg List.length e2
        rw [List.length_map] at this
        rw [this]; exact rbStep_length_le (by simp; omega) z
      rw [rejBoundedLoop_map η l2 L, e2]
      rfl
  | [] => by
    show Option.map _ (if a.length ≥ n then some a else none) = _
    rw [rbFold, List.length_map]
    by_cases h : a.length = n
    · rw [ifT (by omega), ifT h]; rfl
    · rw [ifF (by omega), ifF h]; rfl

/-- `RejBoundedPoly(ρ)` as a polynomial of `R_q`, when the loop over the
`B` bytes of output samples 256 coefficients. -/
theorem rejBounded_some (η : Nat) {ρ : List Byte} {B : Nat} (h : (rbFold η [] (H ρ B)).length = 256) :
    (rejBoundedPoly η B ρ).map toRq = some (toPoly (rbFold η [] (H ρ B))) := by
  have e := rejBoundedLoop_map η (a := []) (by simp) (H ρ B)
  simp only [List.map_nil] at e
  rw [ifT h] at e
  simp only [rejBoundedPoly, Option.map_map]
  cases hl : rejBoundedLoop η [] (H ρ B) with
  | none => rw [hl] at e; cases e
  | some a =>
    rw [hl] at e
    simp only [Option.map_some, Option.some.injEq] at e
    simp only [Option.map_some, Function.comp, Option.some.injEq]
    apply Vector.ext
    intro i hi
    simp only [toRq, Vector.getElem_map, Vector.getElem_ofFn, ← e, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases a[i]? <;> rfl

/-- If the loop over `B` bytes of output does not sample 256 coefficients,
neither does it over the first `B'` bytes. -/
theorem rejBounded_none (η : Nat) {ρ : List Byte} {B B' : Nat} (hB : B' ≤ B)
    (h : (rbFold η [] (H ρ B)).length ≠ 256) : rejBoundedPoly η B' ρ = none := by
  have e : H ρ B = H ρ B' ++ (H ρ B).drop B' := by rw [← H_take ρ hB, List.take_append_drop]
  rw [e, rbFold_append] at h
  have e' := rejBoundedLoop_map η (a := []) (by simp) (H ρ B')
  simp only [List.map_nil] at e'
  by_cases hf : (rbFold η [] (H ρ B')).length = n
  · exact absurd (by rw [rbFold_full hf]; exact hf) h
  · rw [ifF hf] at e'
    rw [rejBoundedPoly]
    cases hl : rejBoundedLoop η [] (H ρ B') with
    | none => rfl
    | some a => rw [hl] at e'; cases e'

/-! ## What the lengths depend on -/

/-- Whether the loop accepts the half-bytes of the byte `z`. -/
def hbOks (η : Nat) (z : Byte) : Nat × Nat := (halfByteOk η (z.toNat % 16), halfByteOk η (z.toNat / 16))

theorem rbStep_length_congr {η : Nat} {a₁ a₂ : List Zq} (ha : a₁.length = a₂.length) {z₁ z₂ : Byte}
    (hz : hbOks η z₁ = hbOks η z₂) : (rbStep η a₁ z₁).length = (rbStep η a₂ z₂).length := by
  simp only [hbOks, Prod.mk.injEq] at hz
  rw [rbStep_length, rbStep_length, ha, hz.1, hz.2]

/-- The number of coefficients sampled from bytes accepted alike. -/
theorem rbFold_length_congr {η : Nat} : ∀ {a₁ a₂ : List Zq} {L₁ L₂ : List Byte}, a₁.length = a₂.length →
    List.map (hbOks η) L₁ = List.map (hbOks η) L₂ → (rbFold η a₁ L₁).length = (rbFold η a₂ L₂).length
  | _, _, [], [], ha, _ => ha
  | _, _, z₁ :: L₁, z₂ :: L₂, ha, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [rbFold, rbFold]
    exact rbFold_length_congr (rbStep_length_congr ha h.1) h.2
  | _, _, [], _ :: _, _, h | _, _, _ :: _, [], _, h => by simp at h

/-- The leak, byte by byte. -/
theorem leak_eq (η : Nat) (L : List Byte) :
    L.flatMap (fun z => [halfByteOk η (z.toNat % 16), halfByteOk η (z.toNat / 16)]) =
      (L.map (hbOks η)).flatMap fun p => [p.1, p.2] := by
  simp [List.flatMap_map, hbOks]

theorem flatMap_pair_inj : ∀ {A B : List (Nat × Nat)},
    A.flatMap (fun p => [p.1, p.2]) = B.flatMap (fun p => [p.1, p.2]) → A = B
  | [], [], _ => rfl
  | a :: A, b :: B, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    rw [Prod.ext h.1 h.2.1, flatMap_pair_inj h.2.2]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- Two seeds with the same leak: their outputs' first `B` bytes (`B` at most
the bytes the leak covers) are accepted alike. -/
theorem leak_hbOks {η : Nat} {ρ₁ ρ₂ : List Byte} (h : rejBoundedLeak η ρ₁ = rejBoundedLeak η ρ₂) {B : Nat}
    (hB : B ≤ maxBounds.rejBounded) : (H ρ₁ B).map (hbOks η) = (H ρ₂ B).map (hbOks η) := by
  simp only [rejBoundedLeak, leak_eq] at h
  have := congrArg (List.take B) (flatMap_pair_inj h)
  rwa [← List.map_take, ← List.map_take, H_take _ hB, H_take _ hB] at this

end VG.Proof.MlDsa.Sample

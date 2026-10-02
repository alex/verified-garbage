import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.MlDsa.Sample.Mem

/-!
# ML-DSA: `RejNTTPoly` three bytes at a time

An implementation that runs the loop of `RejNTTPoly` (Algorithm 30) over a
fixed number of 3-byte arrays of XOF output, doing nothing once it has 256
coefficients, samples `rnFold [] out` (`rnStep` is one iteration). It computes
`RejNTTPoly` if that has 256 coefficients (`rejNTTLoop_eq`), and otherwise so
does no shorter output, the least bound of Appendix C included
(`rejNTT_none`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- The value of the 3 bytes `b₀, b₁, b₂` (Algorithm 14, line 2 and 3). -/
def rnZ (b₀ b₁ b₂ : Byte) : Nat := b₀.toNat + 256 * b₁.toNat + 65536 * (b₂.toNat % 128)

/-- One iteration of the loop of `RejNTTPoly` (lines 5–9 of Algorithm 30),
which does nothing once there are 256 coefficients. -/
def rnStep (a : List Zq) (b₀ b₁ b₂ : Byte) : List Zq :=
  if a.length < n then (if rnZ b₀ b₁ b₂ < q then a ++ [Fin.ofNat q (rnZ b₀ b₁ b₂)] else a) else a

/-- The coefficients after the loop over the whole 3-byte arrays of `L`. -/
def rnFold : List Zq → List Byte → List Zq
  | a, b₀ :: b₁ :: b₂ :: L => rnFold (rnStep a b₀ b₁ b₂) L
  | a, _ => a

theorem coeffFromThreeBytes_eq (b₀ b₁ b₂ : Byte) :
    coeffFromThreeBytes b₀ b₁ b₂ =
      if rnZ b₀ b₁ b₂ < q then some (Fin.ofNat q (rnZ b₀ b₁ b₂)) else none := by
  have e : (2 ^ 16 * (if b₂.toNat > 127 then b₂.toNat - 128 else b₂.toNat) + 2 ^ 8 * b₁.toNat + b₀.toNat) =
      rnZ b₀ b₁ b₂ := by
    have := b₂.isLt
    unfold rnZ; split <;> omega
  simp only [coeffFromThreeBytes, e]
  split
  · rename_i h; exact congrArg some (Fin.ext (Nat.mod_eq_of_lt h).symm)
  · rfl

theorem rnStep_length_le {a : List Zq} (ha : a.length ≤ n) (b₀ b₁ b₂ : Byte) : (rnStep a b₀ b₁ b₂).length ≤ n := by
  unfold rnStep; split
  · split <;> (try simp only [List.length_append, List.length_singleton]) <;> omega
  · exact ha

theorem rnStep_full {a : List Zq} (ha : a.length = n) (b₀ b₁ b₂ : Byte) : rnStep a b₀ b₁ b₂ = a := by
  unfold rnStep; rw [ifF (by omega)]

theorem rnFold_full {a : List Zq} (ha : a.length = n) : ∀ L, rnFold a L = a
  | _ :: _ :: _ :: L => by rw [rnFold, rnStep_full ha, rnFold_full ha L]
  | [] | [_] | [_, _] => rfl

theorem rnFold_length_le {a : List Zq} (ha : a.length ≤ n) : ∀ L, (rnFold a L).length ≤ n
  | _ :: _ :: _ :: L => by rw [rnFold]; exact rnFold_length_le (rnStep_length_le ha _ _ _) L
  | [] | [_] | [_, _] => ha

/-- The loop, as `rnFold`: it succeeds when that has 256 coefficients. -/
theorem rejNTTLoop_eq {a : List Zq} (ha : a.length ≤ n) :
    ∀ L, rejNTTLoop a L = if (rnFold a L).length = n then some (rnFold a L) else none
  | b₀ :: b₁ :: b₂ :: L => by
    rw [rejNTTLoop, rnFold]
    by_cases h : a.length ≥ n
    · rw [ifT h, rnStep_full (by omega), rnFold_full (by omega), ifT (by omega)]
    · rw [ifF h, ← rejNTTLoop_eq (rnStep_length_le ha _ _ _) L, rnStep, ifT (by omega),
        coeffFromThreeBytes_eq]
      by_cases hz : rnZ b₀ b₁ b₂ < q <;> simp only [hz, ↓reduceIte]
  | [] | [_] | [_, _] => by
    show (if a.length ≥ n then some a else none) = if a.length = n then some a else none
    by_cases h : a.length = n
    · rw [ifT (by omega), ifT h]
    · rw [ifF (by omega), ifF h]

/-- The loop over `L₁` then `L₂`, for `L₁` a whole number of 3-byte arrays. -/
theorem rnFold_append (a : List Zq) : ∀ (L₁ L₂ : List Byte), L₁.length % 3 = 0 →
    rnFold a (L₁ ++ L₂) = rnFold (rnFold a L₁) L₂
  | [], _, _ => rfl
  | b₀ :: b₁ :: b₂ :: L₁, L₂, h => by
    simp only [List.cons_append, rnFold]
    exact rnFold_append _ L₁ L₂ (by simp only [List.length_cons] at h; omega)
  | [_], _, h | [_, _], _, h => by simp at h

/-- One more iteration, on the 3 bytes after `L`. -/
theorem rnFold_snoc (a : List Zq) {L : List Byte} (h : L.length % 3 = 0) (b₀ b₁ b₂ : Byte) :
    rnFold a (L ++ [b₀, b₁, b₂]) = rnStep (rnFold a L) b₀ b₁ b₂ := by
  rw [rnFold_append a L _ h]; rfl

/-- `RejNTTPoly(ρ)` with a bound `B`, when the loop over the `B` bytes of
output samples 256 coefficients. -/
theorem rejNTT_some {ρ : List Byte} {B : Nat} (h : (rnFold [] (G ρ B)).length = 256) :
    rejNTTPoly B ρ = some (toPoly (rnFold [] (G ρ B))) := by
  rw [rejNTTPoly, rejNTTLoop_eq (by simp) _, ifT h]
  rfl

/-- If the loop over `B` bytes of output does not sample 256 coefficients,
neither does it over the first `B'` bytes. -/
theorem rejNTT_none {ρ : List Byte} {B B' : Nat} (hB : B' ≤ B) (h3 : B' % 3 = 0)
    (h : (rnFold [] (G ρ B)).length ≠ 256) : rejNTTPoly B' ρ = none := by
  have e : G ρ B = G ρ B' ++ (G ρ B).drop B' := by rw [← G_take ρ hB, List.take_append_drop]
  rw [e, rnFold_append _ _ _ (by rw [G_length]; exact h3)] at h
  rw [rejNTTPoly, rejNTTLoop_eq (by simp) _]
  by_cases hf : (rnFold [] (G ρ B')).length = n
  · exact absurd (by rw [rnFold_full hf]; exact hf) h
  · rw [ifF hf]; rfl

end VG.Proof.MlDsa.Sample

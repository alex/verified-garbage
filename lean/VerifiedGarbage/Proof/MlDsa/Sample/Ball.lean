import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.MlDsa.Sample.Mem

/-!
# ML-DSA: `SampleInBall` a byte at a time

Untrusted: everything here is checked by Lean. An implementation that runs
the loop of `SampleInBall` (Algorithm 29) over a fixed number of bytes of
output, doing nothing once `i = 256`, leaves `bFold τ h (c, i) out`
(`bStep` is one iteration): the polynomial and `i`. It computes
`SampleInBall` if `i` reaches 256 (`sampleInBall_some`), and otherwise so
does no shorter output (`sampleInBall_none`). The sign bits `h` are the bits
of the first 8 bytes of output (`bytesToBits_getD`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- One iteration of the loop of `SampleInBall` (lines 7–12 of Algorithm
29) on the polynomial and `i`, which does nothing once `i = 256`. -/
def bStep (τ : Nat) (h : Array Bool) (st : IPoly × Nat) (j : Byte) : IPoly × Nat :=
  if st.2 < n then
    (if j.toNat > st.2 then st
    else ((st.1.set! st.2 st.1[j.toNat]!).set! j.toNat (if h.getD (st.2 + τ - 256) false then -1 else 1),
      st.2 + 1))
  else st

/-- The polynomial and `i` after the loop over the bytes of `L`. -/
def bFold (τ : Nat) (h : Array Bool) : IPoly × Nat → List Byte → IPoly × Nat
  | st, j :: L => bFold τ h (bStep τ h st j) L
  | st, [] => st

theorem bStep_le {τ : Nat} {h : Array Bool} {st : IPoly × Nat} (hs : st.2 ≤ n) (j : Byte) :
    (bStep τ h st j).2 ≤ n := by
  unfold bStep; split
  · split
    · exact hs
    · rename_i h1 _; exact h1
  · exact hs

theorem bStep_full {τ : Nat} {h : Array Bool} {st : IPoly × Nat} (hs : st.2 = n) (j : Byte) :
    bStep τ h st j = st := by
  unfold bStep; rw [ifF (by omega)]

theorem bFold_full {τ : Nat} {h : Array Bool} {st : IPoly × Nat} (hs : st.2 = n) : ∀ L, bFold τ h st L = st
  | j :: L => by rw [bFold, bStep_full hs, bFold_full hs L]
  | [] => rfl

theorem bFold_le {τ : Nat} {h : Array Bool} {st : IPoly × Nat} (hs : st.2 ≤ n) : ∀ L, (bFold τ h st L).2 ≤ n
  | j :: L => by rw [bFold]; exact bFold_le (bStep_le hs j) L
  | [] => hs

theorem bFold_append (τ : Nat) (h : Array Bool) (st : IPoly × Nat) : ∀ L₁ L₂ : List Byte,
    bFold τ h st (L₁ ++ L₂) = bFold τ h (bFold τ h st L₁) L₂
  | [], _ => rfl
  | j :: L₁, L₂ => by simp only [List.cons_append, bFold]; exact bFold_append τ h _ L₁ L₂

theorem bFold_snoc (τ : Nat) (h : Array Bool) (st : IPoly × Nat) (L : List Byte) (j : Byte) :
    bFold τ h st (L ++ [j]) = bStep τ h (bFold τ h st L) j := by
  rw [bFold_append]; rfl

/-- The loop, as `bFold`: it succeeds when `i` reaches 256. -/
theorem ballLoop_eq (τ : Nat) (h : Array Bool) {c : IPoly} {i : Nat} (hi : i ≤ n) :
    ∀ L, ballLoop τ h c i L = if (bFold τ h (c, i) L).2 = n then some (bFold τ h (c, i) L).1 else none
  | j :: L => by
    rw [ballLoop, bFold]
    by_cases hn : i ≥ n
    · rw [ifT hn, bStep_full (by simp only; omega), bFold_full (by simp only; omega), ifT (by simp only; omega)]
    · rw [ifF hn]
      unfold bStep
      dsimp only
      rw [ifT (show i < n by omega)]
      by_cases hj : j.toNat > i
      · rw [ifT hj, ifT hj]; exact ballLoop_eq τ h hi L
      · rw [ifF hj, ifF hj]; exact ballLoop_eq τ h (by omega) L
  | [] => by
    show (if i ≥ n then some c else none) = if i = n then some c else none
    by_cases hn : i = n
    · rw [ifT (by omega), ifT hn]
    · rw [ifF (by omega), ifF hn]

/-- The sign bits of the output `out`. -/
abbrev signs (out : List Byte) : Array Bool := bytesToBits (out.take 8)

/-- The polynomial and `i` after the loop over the bytes after the first 8. -/
abbrev ballFold (τ : Nat) (out : List Byte) : IPoly × Nat :=
  bFold τ (signs out) (Vector.replicate n 0, 256 - τ) (out.drop 8)

theorem sampleInBall_eq (τ : Nat) {ρ : List Byte} {B : Nat} (hB : 8 ≤ B) :
    sampleInBall τ B ρ =
      if (ballFold τ (H ρ B)).2 = n then some (ballFold τ (H ρ B)).1 else none := by
  rw [sampleInBall]
  rw [ifF (by rw [H_length]; omega), ballLoop_eq τ _ (Nat.sub_le _ _)]

/-- `SampleInBall(ρ)` when `i` reaches 256 in the loop over the `B` bytes of
output. -/
theorem sampleInBall_some (τ : Nat) {ρ : List Byte} {B : Nat} (hB : 8 ≤ B) (h : (ballFold τ (H ρ B)).2 = 256) :
    sampleInBall τ B ρ = some (ballFold τ (H ρ B)).1 := by
  rw [sampleInBall_eq τ hB, ifT h]

/-- If `i` does not reach 256 in the loop over `B` bytes of output, neither
does it over the first `B'` bytes. -/
theorem sampleInBall_none (τ : Nat) {ρ : List Byte} {B B' : Nat} (h8 : 8 ≤ B') (hB : B' ≤ B)
    (h : (ballFold τ (H ρ B)).2 ≠ 256) : sampleInBall τ B' ρ = none := by
  rw [sampleInBall_eq τ h8]
  have e : H ρ B = H ρ B' ++ (H ρ B).drop B' := by rw [← H_take ρ hB, List.take_append_drop]
  have et : (H ρ B).take 8 = (H ρ B').take 8 := by rw [e, List.take_append_of_le_length (by rw [H_length]; omega)]
  have ed : (H ρ B).drop 8 = (H ρ B').drop 8 ++ (H ρ B).drop B' := by
    rw [e, List.drop_append_of_le_length (by rw [H_length]; omega), ← e]
  simp only [ballFold, signs, et, ed, bFold_append] at h
  by_cases hf : (ballFold τ (H ρ B')).2 = n
  · simp only [ballFold, signs] at hf
    exact absurd (by rw [bFold_full hf]; exact hf) h
  · rw [ifF hf]

/-! ## The sign bits -/

theorem testBit_eq (x k : Nat) : x.testBit k = decide (x / 2 ^ k % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  by_cases h : x / 2 ^ k % 2 = 1 <;> simp [h]

/-- Bit `k` of the bytes `z` (for `k < 8 |z|`), as a list. -/
theorem flatBits_getD (z : List Byte) {k : Nat} (hk : k < 8 * z.length) :
    (z.flatMap fun c => (List.range 8).map fun j => decide (c.toNat / 2 ^ j % 2 = 1)).getD k false =
      (z.getD (k / 8) 0).getLsbD (k % 8) := by
  induction z generalizing k with
  | nil => simp at hk
  | cons c z ih =>
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD]
    by_cases h8 : k < 8
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range h8]
      simp only [Option.map_some, Option.getD_some, Nat.div_eq_of_lt h8, List.getD_cons_zero,
        Nat.mod_eq_of_lt h8, BitVec.getLsbD, testBit_eq]
    · rw [List.getElem?_append_right (by simp; omega), List.length_map, List.length_range,
        ← List.getD_eq_getElem?_getD, ih (by simp at hk; omega), show k / 8 = (k - 8) / 8 + 1 by omega,
        List.getD_cons_succ, show k % 8 = (k - 8) % 8 by omega]

/-- Bit `k` of the bytes `z` (for `k < 8 |z|`). -/
theorem bytesToBits_getD (z : List Byte) {k : Nat} (hk : k < 8 * z.length) :
    (bytesToBits z).getD k false = (z.getD (k / 8) 0).getLsbD (k % 8) := by
  rw [bytesToBits, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  exact flatBits_getD z hk

end VG.Proof.MlDsa.Sample

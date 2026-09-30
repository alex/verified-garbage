import VerifiedGarbage.TCB.AArch64.Isa

/-! Basic lane identities for AArch64 SIMD proofs. -/

namespace VG.AArch64

theorem vword_ofVWords (w0 w1 w2 w3 : BitVec 32) {e : Nat} (he : e < 4) :
    vword (ofVWords w0 w1 w2 w3) e = [w0, w1, w2, w3][e] := by
  ext i hi
  simp only [vword, ofVWords, BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp +arith [hi]

/-- Two vectors with the same lanes are the same. -/
theorem vec_ext {x y : BitVec 128} (h : ∀ e < 4, vword x e = vword y e) : x = y := by
  ext i hi
  have := congrArg (fun w : BitVec 32 => w.getLsbD (i % 32)) (h (i / 32) (by omega))
  simp only [vword, BitVec.getLsbD_extractLsb', show i % 32 < 32 by omega, decide_true,
    Bool.true_and, show 32 * (i / 32) + i % 32 = i by omega] at this
  simpa [BitVec.getElem_eq_testBit_toNat, BitVec.getLsbD] using this

theorem ofVWords_vword (x : BitVec 128) : ofVWords (vword x 0) (vword x 1) (vword x 2) (vword x 3) = x :=
  vec_ext fun e he => by
    rw [vword_ofVWords _ _ _ _ he]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- The lanes of the result of an operation on the lanes of two vectors. -/
theorem vword_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat}
    (he : e < 4) : vword (VArr.s4.map2 f x y) e = f 32 (vword x e) (vword y e) := by
  simp only [VArr.map2]
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl


theorem vword_ofVWords_0 (a b c d : BitVec 32) : vword (ofVWords a b c d) 0 = a :=
  vword_ofVWords a b c d (by decide)
theorem vword_ofVWords_1 (a b c d : BitVec 32) : vword (ofVWords a b c d) 1 = b :=
  vword_ofVWords a b c d (by decide)
theorem vword_ofVWords_2 (a b c d : BitVec 32) : vword (ofVWords a b c d) 2 = c :=
  vword_ofVWords a b c d (by decide)
theorem vword_ofVWords_3 (a b c d : BitVec 32) : vword (ofVWords a b c d) 3 = d :=
  vword_ofVWords a b c d (by decide)

theorem setLane_four (v : BitVec 128) (a b c d : BitVec 32) :
    setLane (setLane (setLane (setLane v 32 0 a) 32 1 b) 32 2 c) 32 3 d = ofVWords a b c d := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [setLane, ofVWords, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append,
    hj, decide_true, Bool.true_and, Nat.reduceMul, Nat.sub_zero]
  by_cases h0 : j < 32
  · simp (disch := omega) [h0, decide_eq_true]
  by_cases h1 : j < 64
  · simp (disch := omega) [h0, h1, decide_eq_true, show j - 32 < 32 by omega]
  by_cases h2 : j < 96
  · simp (disch := omega) [h0, h1, h2, decide_eq_true,
      show ¬ j - 32 < 32 by omega, show j - 32 - 32 = j - 64 by omega, show j - 64 < 32 by omega]
  · simp (disch := omega) [h0, h1, h2, decide_eq_true, decide_eq_false,
      show ¬ j - 32 < 32 by omega, show ¬ j - 32 - 32 < 32 by omega,
      show j - 32 - 32 - 32 = j - 96 by omega]

/-- Bit `r` of block `k` of `x ++ y`, blocks being `n` bits wide. -/
theorem getLsbD_append_block {w n : Nat} (x : BitVec w) (y : BitVec n) (k : Nat) {r : Nat} (hr : r < n) :
    (x ++ y).getLsbD (n * k + r) = if k = 0 then y.getLsbD r else x.getLsbD (n * (k - 1) + r) := by
  rw [BitVec.getLsbD_append]
  by_cases hk : k = 0
  · subst hk; simp [hr]
  · have h : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
    simp only [hk, show ¬ n * k + r < n by omega, ↓reduceIte]
    exact congrArg _ (by rw [Nat.mul_sub_one, Nat.sub_add_comm h])

theorem getLsbD_ofVBytes (f : Nat → BitVec 8) {k r : Nat} (hk : k < 16) (hr : r < 8) :
    (ofVBytes f).getLsbD (8 * k + r) = (f k).getLsbD r := by
  simp only [ofVBytes, getLsbD_append_block _ _ _ hr]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by omega)
  all_goals
    simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]

theorem vbyte_ofVBytes (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) : vbyte (ofVBytes f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  exact getLsbD_ofVBytes f hi hr

end VG.AArch64

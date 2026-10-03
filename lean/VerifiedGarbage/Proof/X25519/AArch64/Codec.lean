import VerifiedGarbage.Proof.X25519.AArch64.Arith
import VerifiedGarbage.Impl.X25519.AArch64

/-!
# X25519 on AArch64: decoding and encoding, as numbers

The u-coordinate's four 64-bit words cut into fifteen 17-bit limbs (the top
bit left out), and the full reduction and packing of the result.
-/

namespace VG.Proof.X25519.AArch64

open VG.Spec.X25519 VG.Proof.X25519

/-- The number of four 64-bit words. -/
def uN (w0 w1 w2 w3 : Nat) : Nat := w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3

/-- The limbs of a number are its digits in radix `2¹⁷`. -/
theorem valN_digits (N : Nat) (n : Nat) : valN (fun i => N / 2 ^ (17 * i) % 2 ^ 17) n = N % 2 ^ (17 * n) := by
  induction n with
  | zero => simp [valN, Nat.mod_one]
  | succ n ih =>
    rw [valN, ih, show 17 * (n + 1) = 17 * n + 17 by omega, Nat.pow_add, Nat.mod_mul,
      Nat.mul_comm (N / 2 ^ (17 * n) % 2 ^ 17)]

/-- Limb `i` of the u-coordinate, as `limbOf i` computes it from the words `w`. -/
def ulimb (w : Nat → Nat) (i : Nat) : Nat :=
  if 17 * i % 64 + 17 ≤ 64 then w (17 * i / 64) / 2 ^ (17 * i % 64) % 2 ^ 17
  else (w (17 * i / 64) / 2 ^ (17 * i % 64) + w (17 * i / 64 + 1) * 2 ^ (64 - 17 * i % 64) % 2 ^ 64) % 2 ^ 64 %
    2 ^ 17

theorem ulimb_eq {w : Nat → Nat} (h0 : w 0 < 2 ^ 64) (h1 : w 1 < 2 ^ 64) (h2 : w 2 < 2 ^ 64) : ∀ i < 15, ulimb w i = uN (w 0) (w 1) (w 2) (w 3) / 2 ^ (17 * i) % 2 ^ 17 := by
  intro i hi
  simp only [uN]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
    i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [ulimb, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub,
    Nat.reducePow, Nat.reduceLeDiff, ite_true, ite_false, Nat.pow_zero, Nat.div_one] <;> omega

/-! ## The full reduction -/

/-- The carry out of `x + 19` (limbs `f`), as `quot` computes it. -/
def quotN (f : Nat → Nat) : Nat → Nat
  | 0 => (f 0 + 19) % 2 ^ 64 / 2 ^ 17
  | n + 1 => (f (n + 1) + quotN f n) % 2 ^ 64 / 2 ^ 17

/-- `19 q` added to limb 0. -/
def add19 (f : Nat → Nat) (q : Nat) (i : Nat) : Nat := if i = 0 then (f 0 + q * 19) % 2 ^ 64 else f i

/-- Limb 14 cut to 17 bits (bit 255 and above dropped). -/
def maskTop (f : Nat → Nat) (i : Nat) : Nat := if i = 14 then f 14 % 2 ^ 17 else f i

/-- The two rounds of carries of `freeze`. -/
def twice (f : Nat → Nat) : Nat → Nat := cfold (chainN (cfold (chainN f 14)) 14)

/-- The fully reduced limbs, as `freeze` computes them. -/
def freezeF (f : Nat → Nat) : Nat → Nat :=
  maskTop (chainN (add19 (twice f) (quotN (twice f) 14)) 14)

theorem valN_ge0 (f : Nat → Nat) : ∀ n, 1 ≤ n → f 0 ≤ valN f n
  | 0, h => absurd h (by decide)
  | 1, _ => by simp [valN]
  | n + 2, _ => by
    have := valN_ge0 f (n + 1) (by omega)
    rw [valN]; omega

theorem valN_le {f : Nat → Nat} : ∀ n, 1 ≤ n → (∀ i, 1 ≤ i → i < n → f i < 2 ^ 17) →
    valN f n + 2 ^ 17 ≤ f 0 + 2 ^ (17 * n)
  | 0, h, _ => absurd h (by decide)
  | 1, _, _ => by simp [valN]
  | n + 2, _, h => by
    have ih := valN_le (n + 1) (by omega) fun i h1 h2 => h i h1 (by omega)
    have hn := h (n + 1) (by omega) (by omega)
    rw [valN]
    have : f (n + 1) * 2 ^ (17 * (n + 1)) + 2 ^ (17 * (n + 1)) ≤ 2 ^ 17 * 2 ^ (17 * (n + 1)) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hn
    rw [show 17 * (n + 2) = 17 + 17 * (n + 1) by omega, Nat.pow_add]
    omega

theorem quotN_eq {f : Nat → Nat} (hf : ∀ i < 15, f i < 2 ^ 17) :
    ∀ n < 15, quotN f n = (valN f (n + 1) + 19) / 2 ^ (17 * (n + 1)) := by
  intro n hn
  induction n with
  | zero =>
    have := hf 0 (by decide)
    simp only [quotN, valN, Nat.zero_add, Nat.mul_one, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    rw [Nat.mod_eq_of_lt (by omega)]
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := hf (n + 1) hn
    have hv : valN f (n + 1) < 2 ^ (17 * (n + 1)) := valN_lt fun i hi => hf i (by omega)
    have hq : (valN f (n + 1) + 19) / 2 ^ (17 * (n + 1)) ≤ 1 := by
      have : 19 ≤ 2 ^ (17 * (n + 1)) :=
        Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (by omega : 5 ≤ 17 * (n + 1)))
      rw [Nat.div_le_iff_le_mul_add_pred (Nat.two_pow_pos _)]; omega
    rw [quotN, h1, Nat.mod_eq_of_lt (by omega),
      show valN f (n + 1 + 1) = valN f (n + 1) + f (n + 1) * 2 ^ (17 * (n + 1)) from rfl,
      show 17 * (n + 1 + 1) = 17 * (n + 1) + 17 by omega,
      Nat.pow_add, ← Nat.div_div_eq_div_mul, show valN f (n + 1) + f (n + 1) * 2 ^ (17 * (n + 1)) + 19 =
        valN f (n + 1) + 19 + f (n + 1) * 2 ^ (17 * (n + 1)) by omega,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_comm]

theorem valN_limb0 {f g : Nat → Nat} {d : Nat} (h0 : g 0 = f 0 + d) (hi : ∀ i, 0 < i → g i = f i) :
    ∀ n, 1 ≤ n → valN g n = valN f n + d
  | 0, h => absurd h (by decide)
  | 1, _ => by simp [valN, h0]
  | n + 2, _ => by
    show valN g (n + 1) + g (n + 1) * _ = valN f (n + 1) + f (n + 1) * _ + d
    rw [valN_limb0 h0 hi (n + 1) (by omega), hi (n + 1) (by omega)]; omega

theorem valN_split (f : Nat → Nat) : valN f 15 = valN f 14 + f 14 * 2 ^ 238 := rfl

theorem maskTop_valN (f : Nat → Nat) : valN (maskTop f) 15 + 2 ^ 255 * (f 14 / 2 ^ 17) = valN f 15 := by
  rw [valN_split, valN_split, valN_congr (g := f) fun i hi => by
    simp only [maskTop, show i ≠ 14 by omega, ite_false]]
  simp only [maskTop, ite_true]
  omega

/-- `freeze`: from limbs below `2¹⁸`, the limbs of the number modulo `p`. -/
theorem freezeF_spec {f : Nat → Nat} (hf : Bnd f 18) :
    Bnd (freezeF f) 17 ∧ val15 (freezeF f) < P ∧ toFe (val15 (freezeF f)) = toFe (val15 f) := by
  show _ ∧ valN (freezeF f) 15 < P ∧ toFe (valN (freezeF f) 15) = toFe (valN f 15)
  -- the first round of carries
  obtain ⟨a1, a2, -, a4⟩ := chainN_spec (M := 2 ^ 18) (by decide) (fun i hi => Nat.le_of_lt (hf i hi))
    (n := 14) (by decide)
  generalize hg1 : chainN f 14 = g1 at a1 a2 a4
  have a0 := a1 0 (by decide)
  have hfold1 : g1 0 + g1 14 / 2 ^ 17 * 19 < 2 ^ 64 := by omega
  have v1 := cfold_val hfold1
  simp only [val15] at v1
  have p10 : cfold g1 0 = g1 0 + g1 14 / 2 ^ 17 * 19 := by
    simp only [cfold, show (0 : Nat) ≠ 14 by decide, ite_false, ite_true]; exact Nat.mod_eq_of_lt hfold1
  have p1i : ∀ i, 1 ≤ i → i < 15 → cfold g1 i < 2 ^ 17 := fun i h1 h15 => by
    simp only [cfold, show i ≠ 0 by omega]
    split
    · exact Nat.mod_lt _ (by decide)
    · simp only [ite_false]; exact a1 i (by omega)
  generalize hp1 : cfold g1 = p1 at v1 p10 p1i
  -- the second round
  obtain ⟨b1, b2, -, b4⟩ := chainN_spec (f := p1) (M := 2 ^ 17 + 37) (by decide) (fun i hi => by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · omega
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (p1i i h hi) (by decide))) (n := 14) (by decide)
  generalize hg2 : chainN p1 14 = g2 at b1 b2 b4
  have b0 := b1 0 (by decide)
  have hfold2 : g2 0 + g2 14 / 2 ^ 17 * 19 < 2 ^ 64 := by omega
  have v2 := cfold_val hfold2
  simp only [val15] at v2
  have hV1 : valN p1 15 + 2 ^ 17 ≤ p1 0 + 2 ^ (17 * 15) := valN_le 15 (by decide) fun i h1 h2 => p1i i h1 h2
  have hlow : g2 0 + g2 14 * 2 ^ 238 ≤ valN g2 15 := by
    rw [valN_split]; have := valN_ge0 g2 14 (by decide); omega
  have p20 : cfold g2 0 = g2 0 + g2 14 / 2 ^ 17 * 19 := by
    simp only [cfold, show (0 : Nat) ≠ 14 by decide, ite_false, ite_true]; exact Nat.mod_eq_of_lt hfold2
  have p2b : Bnd (cfold g2) 17 := fun i hi => by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · rw [p20]
      rw [b4] at hlow
      simp only [Nat.reduceMul] at hV1
      omega
    · simp only [cfold, show i ≠ 0 by omega]
      split
      · exact Nat.mod_lt _ (by decide)
      · simp only [ite_false]; exact b1 i (by omega)
  generalize hp2 : cfold g2 = p2 at v2 p2b
  -- the carry out of `x + 19`
  have hV2 : valN p2 15 < 2 ^ 255 := valN_lt fun i hi => p2b i hi
  have hq := quotN_eq (f := p2) (fun i hi => p2b i hi) 14 (by decide)
  simp only [Nat.reduceAdd, Nat.reduceMul] at hq
  have hq1 : quotN p2 14 ≤ 1 := by rw [hq]; omega
  have hp30 : p2 0 + quotN p2 14 * 19 < 2 ^ 64 := by have := p2b 0 (by decide); omega
  have v3 : valN (add19 p2 (quotN p2 14)) 15 = valN p2 15 + quotN p2 14 * 19 :=
    valN_limb0 (by simp only [add19, ite_true]; exact Nat.mod_eq_of_lt hp30)
      (fun i hi => by simp only [add19, show i ≠ 0 by omega, ite_false]) 15 (by decide)
  obtain ⟨c1, c2, -, c4⟩ := chainN_spec (f := add19 p2 (quotN p2 14)) (M := 2 ^ 17 + 18) (by decide)
    (fun i hi => by
      simp only [add19]
      split
      · rename_i h; subst h; have := p2b 0 (by decide); rw [Nat.mod_eq_of_lt hp30]; omega
      · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (p2b i hi) (by decide))) (n := 14) (by decide)
  have hr := maskTop_valN (chainN (add19 p2 (quotN p2 14)) 14)
  have rb : Bnd (freezeF f) 17 := fun i hi => by
    simp only [freezeF, twice, hg1, hp1, hg2, hp2, maskTop]
    split
    · exact Nat.mod_lt _ (by decide)
    · exact c1 i (by omega)
  have hR : valN (freezeF f) 15 < 2 ^ 255 := valN_lt fun i hi => rb i hi
  have hF : freezeF f = maskTop (chainN (add19 p2 (quotN p2 14)) 14) := by
    simp only [freezeF, twice, hg1, hp1, hg2, hp2]
  rw [← hF, c4, v3] at hr
  have c14 : chainN (add19 p2 (quotN p2 14)) 14 14 / 2 ^ 17 ≤ 1 := by omega_using [c2]
  have hP : P = 2 ^ 255 - 19 := rfl
  have e1 : valN (freezeF f) 15 + P * quotN p2 14 = valN p2 15 := by
    rw [hP]; omega_using [hr, hq, hV2, hR, c14]
  have e2 : valN (freezeF f) 15 < P := by
    rcases (by omega_using [hq1] : quotN p2 14 = 0 ∨ quotN p2 14 = 1) with h | h
    · rw [h] at e1 hq
      rw [hP]; omega_using [e1, hq]
    · rw [h] at e1
      rw [hP] at e1 ⊢; omega_using [e1, hV2]
  refine ⟨rb, e2, ?_⟩
  have t1 : toFe (valN p2 15) = toFe (valN f 15) := by
    rw [v2, b4, v1, a4]
  rw [← t1]
  refine toFe_congr ?_
  rw [← e1, Nat.add_mul_mod_self_left]

/-! ## Packing -/

/-- Limb `i` shifted to its place in word `j`, as `place` computes it. -/
def placeV (l : Nat → Nat) (i j : Nat) : Nat :=
  if 64 * j ≤ 17 * i then l i * 2 ^ (17 * i - 64 * j) % 2 ^ 64 else l i / 2 ^ (64 * j - 17 * i)

/-- Word `j`, as `packWord j` computes it. -/
def packV (l : Nat → Nat) (j : Nat) : Nat :=
  match Impl.X25519.AArch64.wordLimbs j with
  | [] => 0
  | i :: is => is.foldl (fun acc i => (acc + placeV l i j) % 2 ^ 64) (placeV l i j)

theorem shl_mod (x : Nat) {k : Nat} (hk : k ≤ 64) : x * 2 ^ k % 2 ^ 64 = x % 2 ^ (64 - k) * 2 ^ k := by
  rw [show 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k by rw [← Nat.pow_add, Nat.sub_add_cancel hk],
    Nat.mul_mod_mul_right]

theorem mod64_of_lt {x : Nat} (h : x < 2 ^ 64) : x % 2 ^ 64 = x := Nat.mod_eq_of_lt h

theorem packV_words {l : Nat → Nat} (hl : Bnd l 17) :
    packV l 0 = l 0 + l 1 * 2 ^ 17 + l 2 * 2 ^ 34 + l 3 % 2 ^ 13 * 2 ^ 51 ∧
    packV l 1 = l 3 / 2 ^ 13 + l 4 * 2 ^ 4 + l 5 * 2 ^ 21 + l 6 * 2 ^ 38 + l 7 % 2 ^ 9 * 2 ^ 55 ∧
    packV l 2 = l 7 / 2 ^ 9 + l 8 * 2 ^ 8 + l 9 * 2 ^ 25 + l 10 * 2 ^ 42 + l 11 % 2 ^ 5 * 2 ^ 59 ∧
    packV l 3 = l 11 / 2 ^ 5 + l 12 * 2 ^ 12 + l 13 * 2 ^ 29 + l 14 * 2 ^ 46 := by
  have h0 := hl 0 (by decide); have h1 := hl 1 (by decide); have h2 := hl 2 (by decide)
  have h3 := hl 3 (by decide); have h4 := hl 4 (by decide); have h5 := hl 5 (by decide)
  have h6 := hl 6 (by decide); have h7 := hl 7 (by decide); have h8 := hl 8 (by decide)
  have h9 := hl 9 (by decide); have h10 := hl 10 (by decide); have h11 := hl 11 (by decide)
  have h12 := hl 12 (by decide); have h13 := hl 13 (by decide); have h14 := hl 14 (by decide)
  have w0 : Impl.X25519.AArch64.wordLimbs 0 = [0, 1, 2, 3] := by decide
  have w1 : Impl.X25519.AArch64.wordLimbs 1 = [3, 4, 5, 6, 7] := by decide
  have w2 : Impl.X25519.AArch64.wordLimbs 2 = [7, 8, 9, 10, 11] := by decide
  have w3 : Impl.X25519.AArch64.wordLimbs 3 = [11, 12, 13, 14] := by decide
  have e0 : packV l 0 = (((placeV l 0 0 + placeV l 1 0) % 2 ^ 64 + placeV l 2 0) % 2 ^ 64 +
      placeV l 3 0) % 2 ^ 64 := by
    unfold packV; rw [w0]; dsimp only; rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  have e1 : packV l 1 = ((((placeV l 3 1 + placeV l 4 1) % 2 ^ 64 + placeV l 5 1) % 2 ^ 64 +
      placeV l 6 1) % 2 ^ 64 + placeV l 7 1) % 2 ^ 64 := by
    unfold packV; rw [w1]; dsimp only
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  have e2 : packV l 2 = ((((placeV l 7 2 + placeV l 8 2) % 2 ^ 64 + placeV l 9 2) % 2 ^ 64 +
      placeV l 10 2) % 2 ^ 64 + placeV l 11 2) % 2 ^ 64 := by
    unfold packV; rw [w2]; dsimp only
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  have e3 : packV l 3 = (((placeV l 11 3 + placeV l 12 3) % 2 ^ 64 + placeV l 13 3) % 2 ^ 64 +
      placeV l 14 3) % 2 ^ 64 := by
    unfold packV; rw [w3]; dsimp only; rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  rw [e0, e1, e2, e3]
  simp only [placeV, Nat.reduceMul, Nat.reduceLeDiff, ite_true, ite_false, Nat.reduceSub, Nat.pow_zero,
    Nat.mul_one]
  rw [shl_mod (l 3) (k := 51) (by decide), shl_mod (l 7) (k := 55) (by decide),
    shl_mod (l 11) (k := 59) (by decide)]
  simp only [Nat.reduceSub]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [mod64_of_lt]

theorem digits4 {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (h2 : w2 < 2 ^ 64)
    (h3 : w3 < 2 ^ 64) : ∀ j < 4, (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3) / 2 ^ (64 * j) % 2 ^ 64 =
      [w0, w1, w2, w3].getD j 0 := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simp only [List.getD_cons_zero]; omega
  · simp only [List.getD_cons_succ, List.getD_cons_zero]; omega
  · simp only [List.getD_cons_succ, List.getD_cons_zero]; omega
  · simp only [List.getD_cons_succ, List.getD_cons_zero]; omega

theorem packV_eq {l : Nat → Nat} (hl : Bnd l 17) : ∀ j < 4, packV l j = valN l 15 / 2 ^ (64 * j) % 2 ^ 64 := by
  obtain ⟨w0, w1, w2, w3⟩ := packV_words hl
  have h0 := hl 0 (by decide); have h1 := hl 1 (by decide); have h2 := hl 2 (by decide)
  have h3 := hl 3 (by decide); have h4 := hl 4 (by decide); have h5 := hl 5 (by decide)
  have h6 := hl 6 (by decide); have h7 := hl 7 (by decide); have h8 := hl 8 (by decide)
  have h9 := hl 9 (by decide); have h10 := hl 10 (by decide); have h11 := hl 11 (by decide)
  have h12 := hl 12 (by decide); have h13 := hl 13 (by decide); have h14 := hl 14 (by decide)
  have b0 : packV l 0 < 2 ^ 64 := by rw [w0]; omega_using [h0, h1, h2]
  have b1 : packV l 1 < 2 ^ 64 := by rw [w1]; omega_using [h3, h4, h5, h6]
  have b2 : packV l 2 < 2 ^ 64 := by rw [w2]; omega_using [h7, h8, h9, h10]
  have b3 : packV l 3 < 2 ^ 64 := by rw [w3]; omega_using [h11, h12, h13, h14]
  have e3 : l 3 * 2 ^ 51 = l 3 % 2 ^ 13 * 2 ^ 51 + 2 ^ 64 * (l 3 / 2 ^ 13) := by
    conv => lhs; rw [← Nat.div_add_mod (l 3) (2 ^ 13)]
    grind
  have e7 : l 7 * 2 ^ 119 = 2 ^ 64 * (l 7 % 2 ^ 9 * 2 ^ 55) + 2 ^ 128 * (l 7 / 2 ^ 9) := by
    conv => lhs; rw [← Nat.div_add_mod (l 7) (2 ^ 9)]
    grind
  have e11 : l 11 * 2 ^ 187 = 2 ^ 128 * (l 11 % 2 ^ 5 * 2 ^ 59) + 2 ^ 192 * (l 11 / 2 ^ 5) := by
    conv => lhs; rw [← Nat.div_add_mod (l 11) (2 ^ 5)]
    grind
  have hv : valN l 15 = packV l 0 + 2 ^ 64 * packV l 1 + 2 ^ 128 * packV l 2 + 2 ^ 192 * packV l 3 := by
    rw [w0, w1, w2, w3]
    simp only [valN, Nat.reduceMul, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    rw [e3, e7, e11]
    grind
  intro j hj
  rw [hv, digits4 b0 b1 b2 b3 j hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp only [List.getD_cons_succ, List.getD_cons_zero]

end VG.Proof.X25519.AArch64

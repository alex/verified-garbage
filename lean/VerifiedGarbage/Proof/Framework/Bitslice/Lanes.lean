import VerifiedGarbage.Proof.Framework.Bitslice.Dom

/-!
# The lane domain: linear layers as XORs of input bits

Linear layers (bit-matrix transposes, ShiftRows, MixColumns, round keys)
move and XOR the bits of words, and mask them with constants. Their effect
is tracked exactly by writing every bit of every `w`-bit word as a constant
bit XOR the XOR of some input bits (*atoms*, numbered from 0). An abstract
word is a pair `(c, f)`: `c` holds the constant bits, and `f` the atoms of
all bit positions at once, in *lanes* of `w` bits, one per atom: bit
`w * a + q` of `f` says whether atom `a` is in the XOR of bit `q`.

XOR, rotations, shifts and masking by constants then act on all the lanes
at once, with a few shifts, ANDs and ORs of the whole numbers, which the
kernel evaluates natively (on GMP numbers) instead of walking lists. `and`
and `or` need one side to be a constant word.

`LaneRel w k A` relates abstract to concrete words, for the assignment `A`
of the `2 ^ k` atoms (bit `a` of `A` is the value of atom `a`).
-/

namespace VG.Bitslice

/-! ## Lanes -/

/-- `c` repeated in the `2 ^ k` lanes of `w` bits. -/
def rep (w c : Nat) : Nat → Nat
  | 0 => c
  | k + 1 => rep w c k ||| rep w c k <<< (w * 2 ^ k)

theorem testBit_ge_of_lt {c w i : Nat} (hc : c < 2 ^ w) (hi : w ≤ i) : c.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hi))

theorem testBit_rep {w c : Nat} (hc : c < 2 ^ w) (k i : Nat) :
    (rep w c k).testBit i = (decide (i < w * 2 ^ k) && c.testBit (i % w)) := by
  induction k generalizing i with
  | zero =>
    simp only [rep, Nat.pow_zero, Nat.mul_one]
    by_cases hi : i < w
    · simp [hi, Nat.mod_eq_of_lt hi]
    · simp [hi, testBit_ge_of_lt hc (Nat.le_of_not_lt hi)]
  | succ k ih =>
    simp only [rep, Nat.testBit_or, Nat.testBit_shiftLeft, ih]
    have e : w * 2 ^ (k + 1) = w * 2 ^ k + w * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two, Nat.mul_add]
    rw [e]
    generalize hW : w * 2 ^ k = W
    by_cases h1 : i < W
    · simp [h1, show i < W + W by omega, show ¬ W ≤ i by omega]
    · have hm : (i - W) % w = i % w := by
        rw [← hW]; exact Nat.sub_mul_mod (by omega)
      by_cases h2 : i < W + W
      · simp [h1, h2, show W ≤ i by omega, show i - W < W by omega, hm]
      · simp [h1, h2, show ¬ i - W < W by omega]

theorem lane_lt {a n w q : Nat} (ha : a < n) (hq : q < w) : w * a + q < w * n := by
  have : w * (a + 1) ≤ w * n := Nat.mul_le_mul_left w ha
  rw [Nat.mul_add, Nat.mul_one] at this; omega

theorem lane_ge {a n w q : Nat} (ha : n ≤ a) : w * n ≤ w * a + q :=
  Nat.le_trans (Nat.mul_le_mul_left w ha) (Nat.le_add_right _ _)

theorem testBit_rep_lane {w c : Nat} (hc : c < 2 ^ w) (k a : Nat) {q : Nat} (hq : q < w) :
    (rep w c k).testBit (w * a + q) = (decide (a < 2 ^ k) && c.testBit q) := by
  rw [testBit_rep hc, Nat.mul_add_mod, Nat.mod_eq_of_lt hq]
  by_cases ha : a < 2 ^ k
  · simp [ha, lane_lt ha hq]
  · simp [ha, Nat.not_lt.mpr (lane_ge (q := q) (w := w) (Nat.le_of_not_lt ha))]

theorem two_pow_sub_one_lt {m w : Nat} (h : m ≤ w) : 2 ^ m - 1 < 2 ^ w :=
  Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos m) (by omega)) (Nat.pow_le_pow_right (by omega) h)

theorem high_mask_lt {m w : Nat} (h : m ≤ w) : (2 ^ m - 1) <<< (w - m) < 2 ^ w := by
  rw [Nat.shiftLeft_eq]
  have : 2 ^ w = 2 ^ m * 2 ^ (w - m) := by rw [← Nat.pow_add]; congr 1; omega
  rw [this]
  exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos m) (by omega)) (Nat.two_pow_pos _)

/-- Every lane rotated right by `m < w` bits. -/
def rotL (w k m f : Nat) : Nat :=
  ((f >>> m) &&& rep w (2 ^ (w - m) - 1) k) ||| ((f <<< (w - m)) &&& rep w ((2 ^ m - 1) <<< (w - m)) k)

theorem testBit_rotL {w k m f a q : Nat} (hm : m < w) (hq : q < w) (ha : a < 2 ^ k) :
    (rotL w k m f).testBit (w * a + q) = f.testBit (w * a + (q + m) % w) := by
  simp only [rotL, Nat.testBit_or, Nat.testBit_and,
    testBit_rep_lane (two_pow_sub_one_lt (Nat.sub_le w m)) k a hq,
    testBit_rep_lane (high_mask_lt (Nat.le_of_lt hm)) k a hq, ha, decide_true, Bool.true_and,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : q + m < w
  · rw [Nat.mod_eq_of_lt h]
    simp [show q < w - m by omega, show ¬ w - m ≤ q by omega, show m + (w * a + q) = w * a + (q + m) by omega]
  · rw [show (q + m) % w = q + m - w by
      rw [show q + m = (q + m - w) + w by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega]
    simp [show ¬ q < w - m by omega, show w - m ≤ q by omega, show q - (w - m) < m by omega,
      show w - m ≤ w * a + q by omega, show w * a + q - (w - m) = w * a + (q + m - w) by omega]

/-- Every lane shifted right by `n ≤ w` bits. -/
def shrL (w k n f : Nat) : Nat := (f >>> n) &&& rep w (2 ^ (w - n) - 1) k

theorem testBit_shrL {w k n f a q : Nat} (hq : q < w) (ha : a < 2 ^ k) :
    (shrL w k n f).testBit (w * a + q) = (decide (q + n < w) && f.testBit (w * a + (q + n))) := by
  simp only [shrL, Nat.testBit_and, testBit_rep_lane (two_pow_sub_one_lt (Nat.sub_le w n)) k a hq,
    ha, decide_true, Bool.true_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases h : q + n < w
  · simp [h, show q < w - n by omega, show n + (w * a + q) = w * a + (q + n) by omega]
  · simp [h, show ¬ q < w - n by omega]

/-! ## Values -/

/-- The XOR of the atoms `a < n` in lane position `q` of `f`, under the assignment `A`. -/
def par (w A f q : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => par w A f q n ^^ (f.testBit (w * n + q) && A.testBit n)

theorem par_congr {w A f g q q' n : Nat} (h : ∀ a < n, f.testBit (w * a + q) = g.testBit (w * a + q')) :
    par w A f q n = par w A g q' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [par, ih fun a ha => h a (by omega), h n (by omega)]

theorem par_xor (w A f g q n : Nat) : par w A (f ^^^ g) q n = (par w A f q n ^^ par w A g q n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [par, ih, Nat.testBit_xor]
    cases par w A f q n <;> cases par w A g q n <;> cases f.testBit (w * n + q) <;>
      cases g.testBit (w * n + q) <;> cases A.testBit n <;> rfl

theorem par_zero (w A q n : Nat) : par w A 0 q n = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [par, ih]

theorem par_and_rep {w A f c q n k : Nat} (hc : c < 2 ^ w) (hq : q < w) (hn : n ≤ 2 ^ k) :
    par w A (f &&& rep w c k) q n = (c.testBit q && par w A f q n) := by
  induction n with
  | zero => simp [par]
  | succ n ih =>
    simp only [par, ih (by omega), Nat.testBit_and, testBit_rep_lane hc k n hq,
      show n < 2 ^ k by omega, decide_true, Bool.true_and]
    cases c.testBit q <;> simp

theorem getLsbD_rotateRight_lt {w : Nat} (x : BitVec w) (n q : Nat) (hq : q < w) :
    (x.rotateRight n).getLsbD q = x.getLsbD ((q + n) % w) := by
  have hw : 0 < w := by omega
  have h2 := Nat.mod_lt n hw
  have e : (q + n) % w = (q + n % w) % w := (Nat.add_mod_mod q n w).symm
  rw [BitVec.getLsbD_rotateRight, e]
  split
  · rw [Nat.mod_eq_of_lt (show q + n % w < w by omega), Nat.add_comm]
  · simp only [hq, decide_true, Bool.true_and]
    congr 1
    rw [show q + n % w = (q - (w - n % w)) + w by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show q - (w - n % w) < w by omega)]


/-! ## The domain -/

/-- Words of `w` bits as constant bits and lanes of the `2 ^ k` atoms. -/
def lanes (w k : Nat) : Dom (Nat × Nat) w where
  xor a b := some (a.1 ^^^ b.1, a.2 ^^^ b.2)
  and a b :=
    if a.2 = 0 then some (a.1 &&& b.1, b.2 &&& rep w a.1 k)
    else if b.2 = 0 then some (a.1 &&& b.1, a.2 &&& rep w b.1 k) else none
  or a b := if a.2 = 0 ∧ b.2 = 0 then some (a.1 ||| b.1, 0) else none
  ror n a := if 0 < w then some (rotL w 0 (n % w) a.1, rotL w k (n % w) a.2) else none
  shr n a := if n < w then some (shrL w 0 n a.1, shrL w k n a.2) else some (0, 0)
  const v := some (v.toNat, 0)

/-- Bit `q` of the word is constant bit `q` XOR the atoms of lane position `q`. -/
def LaneRel {w : Nat} (k A : Nat) (a : Nat × Nat) (x : BitVec w) : Prop :=
  a.1 < 2 ^ w ∧ ∀ q < w, x.getLsbD q = (a.1.testBit q ^^ par w A a.2 q (2 ^ k))

theorem rotL_lt {w m c : Nat} (hm : m < w) : rotL w 0 m c < 2 ^ w := by
  apply Nat.or_lt_two_pow
  · exact Nat.lt_of_le_of_lt Nat.and_le_right (by simpa [rep] using two_pow_sub_one_lt (Nat.sub_le w m))
  · exact Nat.lt_of_le_of_lt Nat.and_le_right (by simpa [rep] using high_mask_lt (Nat.le_of_lt hm))

theorem lanes_sound {w k A : Nat} : (lanes w k).Sound (LaneRel k A) where
  xor {a b c x y} ha hb h := by
    simp only [lanes, Option.some.injEq] at h; subst h
    refine ⟨Nat.xor_lt_two_pow ha.1 hb.1, fun q hq => ?_⟩
    simp only [BitVec.getLsbD_xor, ha.2 q hq, hb.2 q hq, Nat.testBit_xor, par_xor]
    cases a.1.testBit q <;> cases b.1.testBit q <;> cases par w A a.2 q (2 ^ k) <;>
      cases par w A b.2 q (2 ^ k) <;> rfl
  and {a b c x y} ha hb h := by
    simp only [lanes] at h
    split at h
    · rename_i h0; simp only [Option.some.injEq] at h; subst h
      refine ⟨Nat.and_lt_two_pow _ hb.1, fun q hq => ?_⟩
      simp only [BitVec.getLsbD_and, ha.2 q hq, hb.2 q hq, Nat.testBit_and,
        par_and_rep ha.1 hq (Nat.le_refl _), h0, par_zero]
      cases a.1.testBit q <;> cases b.1.testBit q <;> cases par w A b.2 q (2 ^ k) <;> rfl
    · split at h
      · rename_i h0; simp only [Option.some.injEq] at h; subst h
        refine ⟨Nat.and_lt_two_pow _ hb.1, fun q hq => ?_⟩
        simp only [BitVec.getLsbD_and, ha.2 q hq, hb.2 q hq, Nat.testBit_and,
          par_and_rep hb.1 hq (Nat.le_refl _), h0, par_zero]
        cases a.1.testBit q <;> cases b.1.testBit q <;> cases par w A a.2 q (2 ^ k) <;> rfl
      · cases h
  or {a b c x y} ha hb h := by
    simp only [lanes] at h
    split at h
    · rename_i h0; simp only [Option.some.injEq] at h; subst h
      refine ⟨Nat.or_lt_two_pow ha.1 hb.1, fun q hq => ?_⟩
      simp [BitVec.getLsbD_or, ha.2 q hq, hb.2 q hq, Nat.testBit_or, h0.1, h0.2, par_zero]
    · cases h
  ror {n a c x} ha h := by
    simp only [lanes] at h
    split at h
    · rename_i hw
      simp only [Option.some.injEq] at h; subst h
      have hm : n % w < w := Nat.mod_lt n hw
      refine ⟨rotL_lt hm, fun q hq => ?_⟩
      have e : (q + n % w) % w = (q + n) % w := Nat.add_mod_mod q n w
      have h1 := testBit_rotL (f := a.1) (k := 0) (a := 0) hm hq (by decide)
      simp only [Nat.mul_zero, Nat.zero_add, e] at h1
      rw [getLsbD_rotateRight_lt x n q hq, ha.2 _ (Nat.mod_lt _ hw), h1]
      congr 1
      exact par_congr fun b hb => by rw [testBit_rotL hm hq hb, e]
    · cases h
  shr {n a c x} ha h := by
    simp only [lanes] at h
    split at h
    · rename_i hn
      simp only [Option.some.injEq] at h; subst h
      refine ⟨Nat.lt_of_le_of_lt Nat.and_le_right
        (by simpa [rep] using two_pow_sub_one_lt (Nat.sub_le w n)), fun q hq => ?_⟩
      have h1 := testBit_shrL (f := a.1) (k := 0) (a := 0) (n := n) hq (by decide)
      simp only [Nat.mul_zero, Nat.zero_add] at h1
      rw [BitVec.getLsbD_ushiftRight, h1]
      by_cases hqn : q + n < w
      · rw [Nat.add_comm n q, ha.2 _ hqn]
        simp only [hqn, decide_true, Bool.true_and]
        congr 1
        exact par_congr fun b hb => by rw [testBit_shrL hq hb]; simp [hqn]
      · rw [BitVec.getLsbD_of_ge x _ (by omega)]
        simp only [hqn, decide_false, Bool.false_and, Bool.false_xor]
        rw [← par_zero w A q (2 ^ k)]
        exact par_congr fun b hb => by rw [testBit_shrL hq hb]; simp [hqn]
    · simp only [Option.some.injEq] at h; subst h
      refine ⟨Nat.two_pow_pos w, fun q hq => ?_⟩
      rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge x _ (by omega)]
      simp [par_zero]
  const {v c} h := by
    simp only [lanes, Option.some.injEq] at h; subst h
    exact ⟨v.isLt, fun q hq => by simp [par_zero, BitVec.testBit_toNat]⟩


/-! ## Words given by their atoms -/

/-- The XOR of the atoms `l` under the assignment `A`. -/
def xorA (A : Nat) (l : List Nat) : Bool := l.foldr (fun a b => A.testBit a ^^ b) false

/-- The lanes holding the atoms `l` at position `q`. -/
def atomsAt (w q : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => 2 ^ (w * a + q) ^^^ atomsAt w q l

/-- The lanes holding the atoms `g q` at each position `q < n`. -/
def mk (w : Nat) (g : Nat → List Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mk w g n ^^^ atomsAt w n (g n)

theorem lane_inj {w a b q q' : Nat} (hq : q < w) (hq' : q' < w) (h : w * a + q = w * b + q') :
    a = b ∧ q = q' := by
  have hw : 0 < w := by omega
  have e1 := congrArg (· % w) h
  have e2 := congrArg (· / w) h
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hq'] at e1
  simp only [Nat.mul_add_div hw, Nat.div_eq_of_lt hq, Nat.div_eq_of_lt hq', Nat.add_zero] at e2
  exact ⟨e2, e1⟩

theorem par_two_pow {w A a q q' : Nat} (hq : q < w) (hq' : q' < w) (n : Nat) :
    par w A (2 ^ (w * a + q')) q n = (decide (q' = q ∧ a < n) && A.testBit a) := by
  induction n with
  | zero => simp [par]
  | succ n ih =>
    simp only [par, ih, Nat.testBit_two_pow]
    by_cases h : w * a + q' = w * n + q
    · obtain ⟨rfl, rfl⟩ := lane_inj hq' hq h
      simp
    · have : ¬ (q' = q ∧ a = n) := fun ⟨e1, e2⟩ => h (by rw [e1, e2])
      simp only [h, decide_false, Bool.false_and, Bool.xor_false]
      by_cases h2 : q' = q ∧ a < n
      · simp [h2, show a < n + 1 by omega]
      · have : ¬ (q' = q ∧ a < n + 1) := fun ⟨e1, e2⟩ =>
          this ⟨e1, by have := fun e => h2 ⟨e1, e⟩; omega⟩
        simp [h2, this]

theorem par_atomsAt {w A q q' n : Nat} (hq : q < w) (hq' : q' < w) (l : List Nat)
    (hl : ∀ a ∈ l, a < n) : par w A (atomsAt w q' l) q n = (decide (q' = q) && xorA A l) := by
  induction l with
  | nil => simp [atomsAt, xorA, par_zero]
  | cons a l ih =>
    simp only [atomsAt, par_xor, par_two_pow hq hq', ih fun b hb => hl b (by simp [hb]), xorA,
      List.foldr_cons, hl a (by simp), and_true]
    cases decide (q' = q) <;> simp

theorem par_mk {w A q n N : Nat} (hq : q < w) (hn : n ≤ w) (g : Nat → List Nat)
    (hg : ∀ q' < n, ∀ a ∈ g q', a < N) : par w A (mk w g n) q N = (decide (q < n) && xorA A (g q)) := by
  induction n with
  | zero => simp [mk, par_zero]
  | succ n ih =>
    simp only [mk, par_xor, ih (by omega) fun q' hq' => hg q' (by omega),
      par_atomsAt hq (show n < w by omega) _ (hg n (by omega))]
    by_cases h : q = n
    · subst h; simp
    · have : n ≠ q := Ne.symm h
      by_cases h2 : q < n
      · simp [h2, this, show q < n + 1 by omega]
      · simp [h2, this, show ¬ q < n + 1 by omega]

end VG.Bitslice

import VerifiedGarbage.Proof.X25519.Field

/-!
# X25519 on 32-bit ARM: numbers of 16-bit limbs

The arithmetic of `Impl/X25519/Arm.lean` on natural numbers: a number of limbs
(`val16`), the limbs of a number carried from sums (`chain`, `out`), a row of
a product (Knuth's algorithm M), the fold of a product's top half (`2²⁵⁶ ≡
38`), the carry out folded in again (`tail`), `4p` as limbs, and the final
reduction.
-/

namespace VG.Proof.X25519.Arm

open VG.Spec.X25519 (P)

/-- The number with the limbs `f 0, …, f (n - 1)` in radix `2¹⁶` (limbs of any
size). -/
def val16 (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => val16 f n + 2 ^ (16 * n) * f n

theorem val16_succ (f : Nat → Nat) (n : Nat) : val16 f (n + 1) = val16 f n + 2 ^ (16 * n) * f n :=
  rfl

theorem pow16_succ (n : Nat) : 2 ^ (16 * (n + 1)) = 2 ^ (16 * n) * 65536 := by
  rw [Nat.mul_succ, Nat.pow_add]

theorem val16_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = g k) → val16 f n = val16 g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [val16_succ, val16_succ, val16_congr (fun k hk => h k (by omega)), h n (by omega)]

theorem val16_lt {f : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k < 65536) → val16 f n < 2 ^ (16 * n)
  | 0, _ => Nat.one_pos
  | n + 1, h => by
    have ih := val16_lt (n := n) fun k hk => h k (by omega)
    have h1 : 2 ^ (16 * n) * f n ≤ 2 ^ (16 * n) * 65535 :=
      Nat.mul_le_mul_left _ (by have := h n (by omega); omega)
    rw [val16_succ, pow16_succ]
    omega

theorem val16_add (f g : Nat → Nat) :
    ∀ n, val16 (fun k => f k + g k) n = val16 f n + val16 g n
  | 0 => rfl
  | n + 1 => by rw [val16_succ, val16_succ, val16_succ, val16_add f g n, Nat.mul_add]; omega

theorem val16_cmul (a : Nat) (f : Nat → Nat) : ∀ n, val16 (fun k => a * f k) n = a * val16 f n
  | 0 => rfl
  | n + 1 => by
    rw [val16_succ, val16_succ, val16_cmul a f n, Nat.mul_add, Nat.mul_left_comm]

theorem val16_append (f : Nat → Nat) (m : Nat) :
    ∀ n, val16 f (m + n) = val16 f m + 2 ^ (16 * m) * val16 (fun k => f (m + k)) n
  | 0 => by simp [val16]
  | n + 1 => by
    rw [← Nat.add_assoc, val16_succ, val16_append f m n, val16_succ, Nat.mul_add (2 ^ (16 * m)),
      ← Nat.mul_assoc, ← Nat.pow_add, Nat.mul_add 16 m n]
    omega

theorem val16_zero_fn : ∀ n, val16 (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by rw [val16_succ, val16_zero_fn n]; rfl

theorem val16_mono (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : val16 f m ≤ val16 f n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [val16_append]; exact Nat.le_add_right _ _

theorem val16_head (f : Nat → Nat) {n : Nat} (hn : 0 < n) : f 0 ≤ val16 f n := by
  have := val16_mono f (m := 1) (n := n) hn
  simp only [val16] at this
  omega

/-- Changing limb 0 by `d`. -/
theorem val16_add_head (f : Nat → Nat) (d : Nat) {n : Nat} (hn : 0 < n) :
    val16 (fun k => if k = 0 then f 0 + d else f k) n = val16 f n + d := by
  have e : val16 (fun k => if k = 0 then f 0 + d else f k) n =
      val16 (fun k => f k + if k = 0 then d else 0) n :=
    val16_congr fun k _ => by by_cases h : k = 0 <;> simp [h]
  rw [e, val16_add]
  congr 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_comm, val16_append, show val16 (fun k => if k = 0 then d else 0) 1 = d by simp [val16]]
  rw [val16_congr (g := fun _ => 0) (fun k _ => by simp), val16_zero_fn, Nat.mul_zero, Nat.add_zero]

/-! ## Carrying -/

/-- The carry into limb `k` of the limbs of `Σ c k 2^(16k) + cin`. -/
def chain (c : Nat → Nat) (cin : Nat) : Nat → Nat
  | 0 => cin
  | k + 1 => (c k + chain c cin k) / 65536

/-- Limb `k` of the limbs of `Σ c k 2^(16k) + cin`. -/
def out (c : Nat → Nat) (cin k : Nat) : Nat := (c k + chain c cin k) % 65536

theorem chain_succ (c : Nat → Nat) (cin k : Nat) :
    chain c cin (k + 1) = (c k + chain c cin k) / 65536 := rfl

theorem out_lt (c : Nat → Nat) (cin k : Nat) : out c cin k < 65536 := Nat.mod_lt _ (by decide)

theorem chain_val (c : Nat → Nat) (cin : Nat) :
    ∀ n, val16 (out c cin) n + 2 ^ (16 * n) * chain c cin n = val16 c n + cin
  | 0 => by simp [val16, chain]
  | n + 1 => by
    have ih := chain_val c cin n
    rw [val16_succ, val16_succ, chain_succ, pow16_succ, out]
    have e : 2 ^ (16 * n) * ((c n + chain c cin n) % 65536) +
        2 ^ (16 * n) * 65536 * ((c n + chain c cin n) / 65536) = 2 ^ (16 * n) * (c n + chain c cin n) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]
    rw [Nat.mul_add] at e
    omega

/-- The carries stay below `2¹⁶` (and each sum below `2³²`) if every sum is at
most `2³² - 2¹⁶`. -/
theorem chain_lt {c : Nat → Nat} {cin n : Nat} (hc : ∀ k < n, c k + 65536 ≤ 2 ^ 32)
    (hcin : cin < 65536) : ∀ k ≤ n, chain c cin k < 65536
  | 0, _ => hcin
  | k + 1, hk => by
    have := chain_lt hc hcin k (by omega)
    have := hc k (by omega)
    rw [chain_succ, Nat.div_lt_iff_lt_mul (by decide)]
    omega

theorem sum_lt {c : Nat → Nat} {cin n : Nat} (hc : ∀ k < n, c k + 65536 ≤ 2 ^ 32)
    (hcin : cin < 65536) {k : Nat} (hk : k < n) : c k + chain c cin k < 2 ^ 32 := by
  have := chain_lt hc hcin k (by omega)
  have := hc k hk
  omega

/-! ## A row of a product -/

/-- Row `i` of a product: the sums `a_i b_j + acc_(i+j)`. -/
def rowC (acc a b : Nat → Nat) (i j : Nat) : Nat := a i * b j + acc (i + j)

/-- The limbs after row `i`: those below `i`, the row's limbs, and its carry. -/
def rowAcc (acc a b : Nat → Nat) (i k : Nat) : Nat :=
  if k < i then acc k else if k < i + 16 then out (rowC acc a b i) 0 (k - i)
  else chain (rowC acc a b i) 0 16

theorem row_val {acc a b : Nat → Nat} {i : Nat} (hv : val16 acc (i + 16) = val16 a i * val16 b 16) :
    val16 (rowAcc acc a b i) (i + 17) = val16 a (i + 1) * val16 b 16 := by
  have e1 : val16 (rowAcc acc a b i) i = val16 acc i :=
    val16_congr fun k hk => by simp [rowAcc, hk]
  have e2 : val16 (fun k => rowAcc acc a b i (i + k)) 17 =
      val16 (out (rowC acc a b i) 0) 16 + 2 ^ 256 * chain (rowC acc a b i) 0 16 := by
    rw [val16_succ, val16_congr (g := out (rowC acc a b i) 0) fun k hk => by
      simp only [rowAcc, show ¬ i + k < i by omega, show i + k < i + 16 by omega, ite_false, ite_true,
        Nat.add_sub_cancel_left]]
    simp only [rowAcc, show ¬ i + 16 < i by omega, Nat.lt_irrefl, ite_false]
  have e3 : val16 (rowC acc a b i) 16 = a i * val16 b 16 + val16 (fun k => acc (i + k)) 16 := by
    rw [← val16_cmul, ← val16_add]; rfl
  have hc := chain_val (rowC acc a b i) 0 16
  rw [show 16 * 16 = 256 from rfl, Nat.add_zero, e3] at hc
  rw [val16_append _ i 17, e1, e2, hc, val16_succ a i, Nat.add_mul, ← hv, val16_append acc i 16,
    Nat.mul_add, Nat.mul_assoc]
  omega

theorem rowC_le {acc a b : Nat → Nat} {i j : Nat} (ha : a i < 65536) (hb : b j < 65536)
    (hacc : acc (i + j) < 65536) : rowC acc a b i j + 65536 ≤ 2 ^ 32 := by
  simp only [rowC]
  have : a i * b j ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem rowAcc_lt {acc a b : Nat → Nat} {i : Nat} (hacc : ∀ k < i, acc k < 65536)
    (hc : ∀ j < 16, rowC acc a b i j + 65536 ≤ 2 ^ 32) :
    ∀ k < i + 17, rowAcc acc a b i k < 65536 := by
  intro k _
  simp only [rowAcc]
  split
  · exact hacc k (by omega)
  · split
    · exact out_lt _ _ _
    · exact chain_lt hc (by decide) 16 (Nat.le_refl _)

/-! ## The fold of a product and the tail -/

/-- The sums `lo_k + 38 hi_k` of a product's limbs. -/
def foldC (acc : Nat → Nat) (k : Nat) : Nat := acc k + 38 * acc (16 + k)

theorem foldC_le {acc : Nat → Nat} (h : ∀ k < 32, acc k < 65536) :
    ∀ k < 16, foldC acc k + 65536 ≤ 2 ^ 32 := by
  intro k hk
  have := h k (by omega)
  have := h (16 + k) (by omega)
  simp only [foldC]
  omega

theorem val16_foldC (acc : Nat → Nat) :
    val16 (foldC acc) 16 = val16 acc 16 + 38 * val16 (fun k => acc (16 + k)) 16 := by
  rw [← val16_cmul, ← val16_add]; rfl

theorem fold_facts {acc : Nat → Nat} (h : ∀ k < 32, acc k < 65536) :
    chain (foldC acc) 0 16 ≤ 38 ∧
      (val16 (out (foldC acc) 0) 16 + 2 ^ 256 * chain (foldC acc) 0 16) % P = val16 acc 32 % P := by
  have hc := chain_val (foldC acc) 0 16
  have hs := val16_append acc 16 16
  have hlo := val16_lt (f := acc) (n := 16) fun k hk => h k (by omega)
  have hhi := val16_lt (f := fun k => acc (16 + k)) (n := 16) fun k hk => h (16 + k) (by omega)
  rw [val16_foldC] at hc
  rw [show 16 * 16 = 256 from rfl] at hc hlo hhi hs
  refine ⟨?_, ?_⟩
  · have : 2 ^ 256 * chain (foldC acc) 0 16 < 2 ^ 256 * 39 := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  · rw [show (16 : Nat) + 16 = 32 from rfl] at hs
    rw [hc, Nat.add_zero, hs, fold256]

/-- The final limbs of `tail`: limb 0 plus 38 times the carry out. -/
def tailL (l : Nat → Nat) (c16 k : Nat) : Nat :=
  if k = 0 then out l (38 * c16) 0 + 38 * chain l (38 * c16) 16 else out l (38 * c16) k

theorem tail_facts {l : Nat → Nat} (hl : ∀ k < 16, l k < 65536) {c16 : Nat} (hc : c16 ≤ 38) :
    chain l (38 * c16) 16 ≤ 1 ∧ (∀ k < 16, tailL l c16 k < 65536) ∧
      val16 (tailL l c16) 16 % P = (val16 l 16 + 2 ^ 256 * c16) % P := by
  have hv := chain_val l (38 * c16) 16
  have hL := val16_lt (f := l) (n := 16) hl
  have hO := val16_lt (f := out l (38 * c16)) (n := 16) fun k _ => out_lt _ _ _
  have h0 := val16_head (out l (38 * c16)) (n := 16) (by decide)
  rw [show 16 * 16 = 256 from rfl] at hv hL hO
  have ht : chain l (38 * c16) 16 ≤ 1 := by
    have : 2 ^ 256 * chain l (38 * c16) 16 < 2 ^ 256 * 2 := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  refine ⟨ht, fun k hk => ?_, ?_⟩
  · simp only [tailL]
    split
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with h | h
      · rw [h]; exact out_lt _ _ _
      · rw [h] at hv ⊢; omega
    · exact out_lt _ _ _
  · have e : val16 (tailL l c16) 16 = val16 (out l (38 * c16)) 16 + 38 * chain l (38 * c16) 16 :=
      val16_add_head (out l (38 * c16)) _ (by decide)
    rw [e, ← fold256, hv, fold256]

/-! ## Sums and differences -/

/-- Limb `k` of `4p`. -/
def fourP (k : Nat) : Nat := if k = 0 then 262068 else if k = 15 then 131068 else 262140

theorem val16_fourP : val16 fourP 16 = 4 * P := by decide

theorem fourP_ge : ∀ k < 16, 65535 ≤ fourP k := by decide

theorem fourP_le : ∀ k < 16, fourP k ≤ 262140 := by decide

/-- The sums of a difference: `a_k + 4p_k - b_k`. -/
def subC (a b : Nat → Nat) (k : Nat) : Nat := a k + fourP k - b k

theorem subC_facts {a b : Nat → Nat} (ha : ∀ k < 16, a k < 65536) (hb : ∀ k < 16, b k < 65536) :
    (∀ k < 16, subC a b k + 65536 ≤ 2 ^ 32) ∧ val16 (subC a b) 16 + val16 b 16 = val16 a 16 + 4 * P := by
  have hK := fourP_ge
  refine ⟨fun k hk => ?_, ?_⟩
  · have := ha k hk; have := hb k hk
    have := fourP_le k hk
    simp only [subC]; omega
  · rw [← val16_add, ← val16_fourP, ← val16_add]
    exact val16_congr fun k hk => by have := hK k hk; have := hb k hk; simp only [subC]; omega

/-- The carry out of the limbs of a sum or difference of numbers below
`2²⁵⁶` is at most 38 (it is at most 2). -/
theorem carry_le {c : Nat → Nat} (h : val16 c 16 < 39 * 2 ^ 256) : chain c 0 16 ≤ 38 := by
  have hv := chain_val c 0 16
  rw [show 16 * 16 = 256 from rfl] at hv
  have : 2 ^ 256 * chain c 0 16 < 2 ^ 256 * 39 := by omega
  have := Nat.lt_of_mul_lt_mul_left this
  omega

/-! ## The final reduction -/

/-- `c` if `sw = 1`, else `a`. -/
def sel {α : Type} (sw : Nat) (a c : α) : α := if sw = 1 then c else a

/-- Limb 15 cut to 15 bits: the number modulo `2²⁵⁵`. -/
def mask15 (l : Nat → Nat) (k : Nat) : Nat := if k = 15 then l 15 % 32768 else l k

theorem mask15_facts {l : Nat → Nat} (hl : ∀ k < 16, l k < 65536) :
    val16 l 16 = val16 (mask15 l) 16 + 2 ^ 255 * (l 15 / 32768) ∧ val16 (mask15 l) 16 < 2 ^ 255 ∧
      (∀ k < 16, mask15 l k < 65536) ∧ l 15 / 32768 ≤ 1 := by
  have e : val16 (mask15 l) 15 = val16 l 15 := val16_congr fun k hk => by simp [mask15, show k ≠ 15 by omega]
  have h15 := hl 15 (by decide)
  have hlo := val16_lt (f := l) (n := 15) fun k hk => hl k (by omega)
  rw [show 16 * 15 = 240 from rfl] at hlo
  have hm : l 15 = l 15 % 32768 + 32768 * (l 15 / 32768) := (Nat.mod_add_div _ _).symm
  refine ⟨?_, ?_, fun k hk => ?_, by omega⟩
  · rw [val16_succ l 15, val16_succ (mask15 l) 15, e, show mask15 l 15 = l 15 % 32768 from rfl,
      show 16 * 15 = 240 from rfl]
    conv => lhs; rw [hm]
    rw [Nat.mul_add, show (2 : Nat) ^ 255 = 2 ^ 240 * 32768 from rfl, Nat.mul_assoc]; omega
  · rw [val16_succ (mask15 l) 15, e, show mask15 l 15 = l 15 % 32768 from rfl, show 16 * 15 = 240 from rfl]
    have : 2 ^ 240 * (l 15 % 32768) ≤ 2 ^ 240 * 32767 :=
      Nat.mul_le_mul_left _ (by have := Nat.mod_lt (l 15) (show 32768 > 0 by decide); omega)
    rw [show (2 : Nat) ^ 255 = 2 ^ 240 * 32768 from rfl]; omega
  · simp only [mask15]; split
    · exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    · exact hl k hk

/-- The limbs of `x' = x mod 2²⁵⁵ + 19 (x >> 255)`. -/
def frA (l : Nat → Nat) : Nat → Nat := out (mask15 l) (19 * (l 15 / 32768))

/-- The limbs of `x' + 19`. -/
def frY (l : Nat → Nat) : Nat → Nat := out (frA l) 19

/-- Whether `x' + 19 ≥ 2²⁵⁵`, that is `x' ≥ p`. -/
def frS (l : Nat → Nat) : Nat := frY l 15 / 32768

/-- The limbs of `x mod p`. -/
def frR (l : Nat → Nat) (k : Nat) : Nat := sel (frS l) (frA l k) (mask15 (frY l) k)

theorem freeze_facts {l : Nat → Nat} (hl : ∀ k < 16, l k < 65536) :
    chain (mask15 l) (19 * (l 15 / 32768)) 16 = 0 ∧ chain (frA l) 19 16 = 0 ∧ frS l ≤ 1 ∧
      (∀ k < 16, frR l k < 65536) ∧ val16 (frR l) 16 = val16 l 16 % P := by
  obtain ⟨e1, b1, lm, c1⟩ := mask15_facts hl
  have hA := chain_val (mask15 l) (19 * (l 15 / 32768)) 16
  rw [show 16 * 16 = 256 from rfl] at hA
  have tA : chain (mask15 l) (19 * (l 15 / 32768)) 16 = 0 := by
    rcases Nat.eq_zero_or_pos (chain (mask15 l) (19 * (l 15 / 32768)) 16) with h | h
    · exact h
    · have : 2 ^ 256 ≤ 2 ^ 256 * chain (mask15 l) (19 * (l 15 / 32768)) 16 := Nat.le_mul_of_pos_right _ h
      omega
  rw [tA, Nat.mul_zero, Nat.add_zero] at hA
  -- `x' = val16 (frA l) 16`.
  have hY := chain_val (frA l) 19 16
  rw [show 16 * 16 = 256 from rfl] at hY
  have hAl : ∀ k < 16, frA l k < 65536 := fun k _ => out_lt _ _ _
  have hYl : ∀ k < 16, frY l k < 65536 := fun k _ => out_lt _ _ _
  have tY : chain (frA l) 19 16 = 0 := by
    rcases Nat.eq_zero_or_pos (chain (frA l) 19 16) with h | h
    · exact h
    · have : 2 ^ 256 ≤ 2 ^ 256 * chain (frA l) 19 16 := Nat.le_mul_of_pos_right _ h
      have : val16 (frA l) 16 = val16 (mask15 l) 16 + 19 * (l 15 / 32768) := hA
      omega
  rw [tY, Nat.mul_zero, Nat.add_zero] at hY
  obtain ⟨e2, b2, lm2, c2⟩ := mask15_facts hYl
  have hxA : val16 (frA l) 16 = val16 (mask15 l) 16 + 19 * (l 15 / 32768) := hA
  have hyv : val16 (frY l) 16 = val16 (frA l) 16 + 19 := hY
  have hP : P = 2 ^ 255 - 19 := rfl
  have hx : val16 l 16 % P = val16 (frA l) 16 % P := by
    rw [e1, hxA, fold255]
  refine ⟨tA, tY, c2, fun k hk => ?_, ?_⟩
  · simp only [frR, sel]; split
    · exact lm2 k hk
    · exact hAl k hk
  · rw [hx]
    have hs : frS l = frY l 15 / 32768 := rfl
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c2 with h0 | h1
    · have e : val16 (frR l) 16 = val16 (frA l) 16 :=
        val16_congr fun k _ => by simp only [frR, sel, hs, h0]; rfl
      rw [e, Nat.mod_eq_of_lt (by rw [h0] at e2; omega)]
    · have e : val16 (frR l) 16 = val16 (mask15 (frY l)) 16 :=
        val16_congr fun k _ => by simp only [frR, sel, hs, h1, ite_true]
      rw [e]
      rw [h1] at e2
      have : val16 (frA l) 16 = val16 (mask15 (frY l)) 16 + P := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The limbs of a number of 16 limbs below `2¹⁶`. -/
theorem val16_div {r : Nat → Nat} {n : Nat} (hr : ∀ k < n, r k < 65536) {k : Nat} (hk : k < n) :
    val16 r n / 2 ^ (16 * k) % 65536 = r k := by
  have e := val16_append r k (n - k)
  rw [Nat.add_sub_cancel' (by omega)] at e
  have e' := val16_append (fun j => r (k + j)) 1 (n - k - 1)
  rw [Nat.add_sub_cancel' (by omega)] at e'
  simp only [val16, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero] at e'
  have hlt := val16_lt (f := r) (n := k) fun j hj => hr j (by omega)
  rw [e, e', Nat.mul_comm (2 ^ (16 * k)), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlt, Nat.zero_add, show (2 : Nat) ^ (16 * 1) = 65536 from rfl, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hr k hk)]

/-- The bytes of a number of 16 limbs below `2¹⁶`. -/
theorem bytes_of_limbs {r : Nat → Nat} (hr : ∀ k < 16, r k < 65536) {k : Nat} (hk : k < 16) :
    val16 r 16 / 256 ^ (2 * k) % 256 = r k % 256 ∧ val16 r 16 / 256 ^ (2 * k + 1) % 256 = r k / 256 := by
  have h := val16_div hr hk
  have p1 : (256 : Nat) ^ (2 * k) = 2 ^ (16 * k) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega
  refine ⟨?_, ?_⟩
  · rw [p1, ← h, Nat.mod_mod_of_dvd _ (by decide)]
  · rw [Nat.pow_succ, p1, ← Nat.div_div_eq_div_mul, ← h, show (65536 : Nat) = 256 * 256 from rfl,
      Nat.mod_mul_right_div_self]

end VG.Proof.X25519.Arm

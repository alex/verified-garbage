import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import VerifiedGarbage.Spec.X25519

/-!
# `2^255 - 19` is prime

A Pratt certificate: for each prime `p` of the tree, a witness `a` of order `p -
1` modulo `p` and the prime factors of `p - 1` (with multiplicity), checked by
Lucas's theorem (`lucas_primality`). The kernel evaluates the modular powers
with `powMod`, a binary exponentiation on `Nat`. Factors below `2^16` are
prime by `norm_num`.
-/

namespace VG.Proof.Ed25519

/-- `b^e % m` for `e < 2^n`, by binary exponentiation. -/
def powMod (m : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | n + 1, b, e => if e = 0 then 1 else
      if e % 2 = 0 then powMod m n (b * b % m) (e / 2) else b * powMod m n (b * b % m) (e / 2) % m

theorem powMod_cast (m : Nat) (n b e : Nat) (he : e < 2 ^ n) :
    (powMod m n b e : ZMod m) = (b : ZMod m) ^ e := by
  induction n generalizing b e with
  | zero =>
    have : e = 0 := by simpa using he
    subst this; simp [powMod]
  | succ n ih =>
    by_cases h0 : e = 0
    · subst h0; simp [powMod]
    have he2 : e / 2 < 2 ^ n := by rw [Nat.pow_succ] at he; omega
    have hb : ((b * b % m : Nat) : ZMod m) = (b : ZMod m) ^ 2 := by
      rw [ZMod.natCast_mod, Nat.cast_mul, sq]
    have hsplit : (b : ZMod m) ^ e = ((b : ZMod m) ^ 2) ^ (e / 2) * (b : ZMod m) ^ (e % 2) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    by_cases h2 : e % 2 = 0
    · simp only [powMod, h0, h2, ite_false, ite_true]
      rw [ih _ _ he2, hb, hsplit, h2, pow_zero, mul_one]
    · simp only [powMod, h0, h2, ite_false]
      have h1 : e % 2 = 1 := by omega
      rw [ZMod.natCast_mod, Nat.cast_mul, ih _ _ he2, hb, hsplit, h1, pow_one, mul_comm]

theorem prime_of_dvd_prod {q : Nat} (hq : q.Prime) {fs : List Nat} (hfs : ∀ f ∈ fs, f.Prime)
    (h : q ∣ fs.prod) : q ∈ fs := by
  induction fs with
  | nil => exact absurd (Nat.eq_one_of_dvd_one (by simpa using h)) hq.ne_one
  | cons f fs ih =>
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (hfs f (by simp))).mp h]; simp
    · exact List.mem_cons_of_mem _ (ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) h)

theorem powMod_lt (m n b e : Nat) (hm : 0 < m) : powMod m n b e < m ∨ powMod m n b e = 1 := by
  induction n generalizing b e with
  | zero => right; rfl
  | succ n ih =>
    simp only [powMod]
    split_ifs
    · right; rfl
    · exact ih _ _
    · left; exact Nat.mod_lt _ hm

/-- Lucas's test, with the prime factors of `p - 1` listed (with multiplicity)
and every power computed by `powMod` with `n`-bit exponents. -/
theorem prime_of_cert (p a n : Nat) (fs : List Nat) (hp : 2 ≤ p) (hn : p - 1 < 2 ^ n)
    (hfs : ∀ f ∈ fs, f.Prime) (hprod : fs.prod = p - 1)
    (ha : powMod p n a (p - 1) = 1)
    (hq : ∀ f ∈ fs, powMod p n a ((p - 1) / f) ≠ 1) : p.Prime := by
  have h1 : ((1 : Nat) : ZMod p) = 1 := Nat.cast_one
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · rw [← powMod_cast p n a _ hn, ha, h1]
  · intro q hq' hd
    have hm := prime_of_dvd_prod hq' hfs (hprod ▸ hd)
    rw [← powMod_cast p n a _ (lt_of_le_of_lt (Nat.div_le_self _ _) hn)]
    intro he
    have hlt := powMod_lt p n a ((p - 1) / q) (by omega)
    rcases hlt with hlt | hlt
    · have := (ZMod.natCast_eq_natCast_iff' _ _ p).mp (he.trans h1.symm)
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at this
      exact hq q hm this
    · exact hq q hm hlt

theorem prime_569003 : Nat.Prime 569003 := by
  refine prime_of_cert 569003 2 20 [2, 7, 97, 419] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_2773320623 : Nat.Prime 2773320623 := by
  refine prime_of_cert 2773320623 5 32 [2, 2437, 569003] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · norm_num
  · norm_num
  · exact prime_569003

theorem prime_72106336199 : Nat.Prime 72106336199 := by
  refine prime_of_cert 72106336199 7 37 [2, 13, 2773320623] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · norm_num
  · norm_num
  · exact prime_2773320623

theorem prime_8574133 : Nat.Prime 8574133 := by
  refine prime_of_cert 8574133 2 24 [2, 2, 3, 7, 103, 991] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_1919519569386763 : Nat.Prime 1919519569386763 := by
  refine prime_of_cert 1919519569386763 2 51 [2, 3, 7, 19, 47, 47, 127, 8574133] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_8574133

theorem prime_75707 : Nat.Prime 75707 := by
  refine prime_of_cert 75707 2 17 [2, 37853] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · norm_num
  · norm_num

theorem prime_75445702479781427272750846543864801 : Nat.Prime 75445702479781427272750846543864801 := by
  refine prime_of_cert 75445702479781427272750846543864801 7 116 [2, 2, 2, 2, 2, 3, 3, 5, 5, 75707, 72106336199, 1919519569386763] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_75707
  · exact prime_72106336199
  · exact prime_1919519569386763

theorem prime_430751 : Nat.Prime 430751 := by
  refine prime_of_cert 430751 17 19 [2, 5, 5, 5, 1723] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_31757755568855353 : Nat.Prime 31757755568855353 := by
  refine prime_of_cert 31757755568855353 10 55 [2, 2, 2, 3, 31, 107, 223, 4153, 430751] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_430751

theorem prime_1923133 : Nat.Prime 1923133 := by
  refine prime_of_cert 1923133 2 21 [2, 2, 3, 43, 3727] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_132049 : Nat.Prime 132049 := by
  refine prime_of_cert 132049 26 18 [2, 2, 2, 2, 3, 3, 7, 131] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_74058212732561358302231226437062788676166966415465897661863160754340907 : Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 := by
  refine prime_of_cert 74058212732561358302231226437062788676166966415465897661863160754340907 2 236 [2, 3, 353, 57467, 132049, 1923133, 31757755568855353, 75445702479781427272750846543864801] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_132049
  · exact prime_1923133
  · exact prime_31757755568855353
  · exact prime_75445702479781427272750846543864801

theorem prime_P : Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  refine prime_of_cert 57896044618658097711785492504343953926634992332820282019728792003956564819949 2 255 [2, 2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_74058212732561358302231226437062788676166966415465897661863160754340907

theorem prime_field : Nat.Prime Spec.X25519.P := by
  rw [show Spec.X25519.P = 57896044618658097711785492504343953926634992332820282019728792003956564819949
    from rfl]
  exact prime_P

instance fact_prime_field : Fact (Nat.Prime Spec.X25519.P) := ⟨prime_field⟩

end VG.Proof.Ed25519

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.Proof.Ed25519.Group.Edwards
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import VerifiedGarbage.Spec.Ed25519
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Nat.Even

/-! Merged from `Proof.Ed25519.Group.Field`. -/
section
/-! Merged from `Proof.Ed25519.Group.Prime`. -/
section
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
end

/-! Merged from `Proof.Ed25519.Group.EdwardsGroup`. -/
section
/-!
# The points of a complete twisted Edwards curve form a commutative group

`EPoint d` is the type of affine points; its addition is the Edwards law of
`Edwards.lean`, its zero `(0, 1)` and its negation `(-x, y)`.
-/

namespace VG.Proof.Ed25519.Edwards

variable {F : Type*} [Field F]

/-- An affine point of the curve. -/
@[ext]
structure EPoint (d : F) where
  x : F
  y : F
  on : OnCurve d x y

variable {d : F}

instance : Zero (EPoint d) := ⟨⟨0, 1, by unfold OnCurve; ring⟩⟩

instance : Neg (EPoint d) := ⟨fun p => ⟨-p.x, p.y, by have := p.on; unfold OnCurve at *; linear_combination this⟩⟩

@[simp] theorem zero_x : (0 : EPoint d).x = 0 := rfl
@[simp] theorem zero_y : (0 : EPoint d).y = 1 := rfl
@[simp] theorem neg_x (p : EPoint d) : (-p).x = -p.x := rfl
@[simp] theorem neg_y (p : EPoint d) : (-p).y = p.y := rfl

variable [hP : Fact (Params d)]

instance : Add (EPoint d) :=
  ⟨fun p q => ⟨addX d p.x p.y q.x q.y, addY d p.x p.y q.x q.y, onCurve_add hP.out p.on q.on⟩⟩

@[simp] theorem add_x (p q : EPoint d) : (p + q).x = addX d p.x p.y q.x q.y := rfl
@[simp] theorem add_y (p q : EPoint d) : (p + q).y = addY d p.x p.y q.x q.y := rfl
theorem add_assoc' (p q r : EPoint d) : p + q + r = p + (q + r) :=
  EPoint.ext (add_assoc_x hP.out p.on q.on r.on) (add_assoc_y hP.out p.on q.on r.on)

theorem zero_add' (p : EPoint d) : 0 + p = p := by
  ext <;> simp [addX, addY]

theorem add_comm' (p q : EPoint d) : p + q = q + p := by
  ext <;> simp only [add_x, add_y, addX, addY] <;> ring_nf

theorem neg_add_cancel' (p : EPoint d) : -p + p = 0 := by
  have h := den_sub_ne hP.out (-p).on p.on
  have hc := p.on
  unfold OnCurve at hc
  ext
  · simp [addX]; ring_nf; simp
  · simp only [add_y, neg_x, neg_y, zero_y, addY] at h ⊢
    rw [div_eq_one_iff_eq h]
    linear_combination hc

instance : AddCommGroup (EPoint d) where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero p := by rw [add_comm', zero_add']
  add_comm := add_comm'
  neg_add_cancel := neg_add_cancel'
  nsmul := nsmulRec
  zsmul := zsmulRec

end VG.Proof.Ed25519.Edwards
end

/-!
# The specification's field as `ZMod P`, and the curve's parameters

`Fe = Fin P` and `ZMod P` are the same type with the same operations, so `toZ`
is the identity; `ZMod P` is a field because `P` is prime (`Prime.lean`). The
specification's `d` is not a square (its power `(P - 1) / 2` is `-1`) and
`sqrtM1` squares to `-1`, so the Edwards addition law over `ZMod P` is
complete.
-/

namespace VG.Proof.Ed25519

open Spec.X25519 (Fe P)
open Edwards

/-- An element of `Fe` as an element of the field `ZMod P`. -/
def toZ (a : Fe) : ZMod P := a

theorem toZ_add (a b : Fe) : toZ (a + b) = toZ a + toZ b := rfl
theorem toZ_sub (a b : Fe) : toZ (a - b) = toZ a - toZ b := rfl
theorem toZ_mul (a b : Fe) : toZ (a * b) = toZ a * toZ b := rfl
theorem toZ_zero : toZ 0 = 0 := rfl
theorem toZ_one : toZ 1 = 1 := rfl
theorem toZ_two : toZ 2 = 2 := rfl
theorem toZ_inj {a b : Fe} : toZ a = toZ b ↔ a = b := Iff.rfl

theorem toZ_pow (a : Fe) (e : Nat) : toZ (Spec.X25519.pow a e) = toZ a ^ e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [Spec.X25519.pow]
    by_cases h0 : e = 0
    · subst h0; rfl
    · simp only [h0, ↓reduceIte]
      have hlt : e / 2 < e := Nat.div_lt_self (by omega) (by decide)
      have hsplit : toZ a ^ e = (toZ a * toZ a) ^ (e / 2) * toZ a ^ (e % 2) := by
        rw [← sq, ← pow_mul, ← pow_add]; congr 1; omega
      by_cases h2 : e % 2 = 0
      · simp only [h2, ↓reduceIte]
        rw [ih _ hlt, toZ_mul, hsplit, h2, pow_zero, mul_one]
      · simp only [h2, ↓reduceIte]
        rw [toZ_mul, ih _ hlt, toZ_mul, hsplit, show e % 2 = 1 by omega, pow_one, mul_comm]

/-- The curve parameter `d` in `ZMod P`. -/
def dZ : ZMod P := toZ Spec.Ed25519.d

private theorem d_val : (Spec.Ed25519.d : Fe).val =
    37095705934669439343138083508754565189542113879843219016388785533085940283555 := by
  decide +kernel

private theorem d_pow : powMod P 256 37095705934669439343138083508754565189542113879843219016388785533085940283555
    ((P - 1) / 2) = P - 1 := by decide +kernel

theorem dZ_pow : dZ ^ ((P - 1) / 2) = -1 := by
  have h : dZ = ((37095705934669439343138083508754565189542113879843219016388785533085940283555 : Nat) :
      ZMod P) := by
    rw [← d_val]; exact (ZMod.natCast_zmod_val _).symm
  rw [h, ← powMod_cast P 256 _ _ (by decide), d_pow, Nat.cast_sub (by decide), ZMod.natCast_self,
    Nat.cast_one, zero_sub]

theorem sqrtM1_sq : Spec.Ed25519.sqrtM1 * Spec.Ed25519.sqrtM1 = 0 - 1 := by decide +kernel

theorem params : Params dZ where
  two := by
    intro h
    have : ((2 : Nat) : ZMod P) = ((0 : Nat) : ZMod P) := by simpa using h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    exact absurd this (by decide)
  sqrtm1 := ⟨toZ Spec.Ed25519.sqrtM1, by
    rw [sq, ← toZ_mul, sqrtM1_sq, toZ_sub, toZ_zero, toZ_one, zero_sub]⟩
  nonsq r hr := by
    have hd : dZ ≠ 0 := by
      intro h; have := dZ_pow; rw [h, zero_pow (by decide)] at this
      exact absurd this (by
        intro h'
        have : ((1 : Nat) : ZMod P) = ((0 : Nat) : ZMod P) := by
          rw [Nat.cast_one, Nat.cast_zero, ← neg_eq_zero, ← h']
        rw [ZMod.natCast_eq_natCast_iff'] at this
        exact absurd this (by decide))
    have hr0 : r ≠ 0 := by rintro rfl; apply hd; rw [← hr]; ring
    have h1 := ZMod.pow_card_sub_one_eq_one hr0
    have h2 := dZ_pow
    rw [← hr, ← pow_mul, show 2 * ((P - 1) / 2) = P - 1 by decide, h1] at h2
    have : ((2 : Nat) : ZMod P) = ((0 : Nat) : ZMod P) := by
      rw [Nat.cast_ofNat, Nat.cast_zero]; linear_combination h2
    rw [ZMod.natCast_eq_natCast_iff'] at this
    exact absurd this (by decide)

instance fact_params : Fact (Params dZ) := ⟨params⟩

end VG.Proof.Ed25519
end

/-!
# The specification's extended coordinates represent points of the group

`Rep p a`: the extended point `p` of the specification (with coordinates in
`Fe`) represents the affine point `a`: `Z ≠ 0`, `X = xZ`, `Y = yZ` and `T =
xyZ`. The specification's addition, scalar multiplication, encoding and
comparison only depend on the points represented, which is what lets an
implementation compute other representatives of the same points.
-/

namespace VG.Proof.Ed25519

open Spec.X25519 (Fe P)
open Spec.Ed25519 (Point)
open Edwards

/-- `p` represents `a`. -/
structure Rep (p : Point) (a : EPoint dZ) : Prop where
  z : toZ p.Z ≠ 0
  x : toZ p.X = a.x * toZ p.Z
  y : toZ p.Y = a.y * toZ p.Z
  t : toZ p.T = a.x * a.y * toZ p.Z

theorem identity_rep : Rep Spec.Ed25519.identity 0 :=
  ⟨by rw [show toZ Spec.Ed25519.identity.Z = 1 from rfl]; exact one_ne_zero,
    by decide, by decide, by decide⟩

section
variable (p q : Point)

theorem pointAdd_X : toZ (Spec.Ed25519.pointAdd p q).X =
    ((toZ p.Y + toZ p.X) * (toZ q.Y + toZ q.X) - (toZ p.Y - toZ p.X) * (toZ q.Y - toZ q.X)) *
      (toZ p.Z * 2 * toZ q.Z - toZ p.T * 2 * dZ * toZ q.T) := rfl

theorem pointAdd_Y : toZ (Spec.Ed25519.pointAdd p q).Y =
    (toZ p.Z * 2 * toZ q.Z + toZ p.T * 2 * dZ * toZ q.T) *
      ((toZ p.Y + toZ p.X) * (toZ q.Y + toZ q.X) + (toZ p.Y - toZ p.X) * (toZ q.Y - toZ q.X)) := rfl

theorem pointAdd_Z : toZ (Spec.Ed25519.pointAdd p q).Z =
    (toZ p.Z * 2 * toZ q.Z - toZ p.T * 2 * dZ * toZ q.T) *
      (toZ p.Z * 2 * toZ q.Z + toZ p.T * 2 * dZ * toZ q.T) := rfl

theorem pointAdd_T : toZ (Spec.Ed25519.pointAdd p q).T =
    ((toZ p.Y + toZ p.X) * (toZ q.Y + toZ q.X) - (toZ p.Y - toZ p.X) * (toZ q.Y - toZ q.X)) *
      ((toZ p.Y + toZ p.X) * (toZ q.Y + toZ q.X) + (toZ p.Y - toZ p.X) * (toZ q.Y - toZ q.X)) := rfl

end

theorem pointAdd_rep {p q : Point} {a b : EPoint dZ} (hp : Rep p a) (hq : Rep q b) :
    Rep (Spec.Ed25519.pointAdd p q) (a + b) := by
  have h2 := params.two
  have ha := den_add_ne params a.on b.on
  have hs := den_sub_ne params a.on b.on
  have hu := mul_inv_cancel₀ ha
  have hv := mul_inv_cancel₀ hs
  have hZ : toZ (Spec.Ed25519.pointAdd p q).Z = 4 * toZ p.Z ^ 2 * toZ q.Z ^ 2 *
      (1 - dZ * a.x * b.x * a.y * b.y) * (1 + dZ * a.x * b.x * a.y * b.y) := by
    rw [pointAdd_Z, hp.t, hq.t]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hZ]
    have h4 : (4 : ZMod P) ≠ 0 := by
      rw [show (4 : ZMod P) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 hp.z))
      (pow_ne_zero 2 hq.z)) hs) ha
  · rw [hZ, pointAdd_X, hp.x, hp.y, hp.t, hq.x, hq.y, hq.t, add_x, addX, div_eq_mul_inv]
    linear_combination (-(4 * toZ p.Z ^ 2 * toZ q.Z ^ 2 * (a.x * b.y + a.y * b.x) *
      (1 - dZ * a.x * b.x * a.y * b.y))) * hu
  · rw [hZ, pointAdd_Y, hp.x, hp.y, hp.t, hq.x, hq.y, hq.t, add_y, addY, div_eq_mul_inv]
    linear_combination (-(4 * toZ p.Z ^ 2 * toZ q.Z ^ 2 * (a.y * b.y + a.x * b.x) *
      (1 + dZ * a.x * b.x * a.y * b.y))) * hv
  · rw [hZ, pointAdd_T, hp.x, hp.y, hq.x, hq.y, add_x, add_y, addX, addY,
      div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-(4 * toZ p.Z ^ 2 * toZ q.Z ^ 2 * (a.x * b.y + a.y * b.x) *
      (a.y * b.y + a.x * b.x) * (1 - dZ * a.x * b.x * a.y * b.y)⁻¹ *
      (1 - dZ * a.x * b.x * a.y * b.y))) * hu +
      (-(4 * toZ p.Z ^ 2 * toZ q.Z ^ 2 * (a.x * b.y + a.y * b.x) * (a.y * b.y + a.x * b.x))) * hv

theorem pointMul_rep (s : Nat) : ∀ {p : Point} {a : EPoint dZ}, Rep p a →
    Rep (Spec.Ed25519.pointMul s p) (s • a) := by
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro p a hp
    rw [Spec.Ed25519.pointMul]
    by_cases h0 : s = 0
    · subst h0; simp only [↓reduceIte, zero_smul]; exact identity_rep
    · simp only [h0, ↓reduceIte]
      have hq := ih (s / 2) (Nat.div_lt_self (by omega) (by decide)) (pointAdd_rep hp hp)
      have hs : s • a = (s / 2) • (a + a) + (s % 2) • a := by
        rw [← two_nsmul, ← mul_nsmul', ← add_nsmul]; congr 1; omega
      by_cases h2 : s % 2 = 0
      · simp only [h2, ↓reduceIte]; rw [hs, h2, zero_smul, add_zero]; exact hq
      · simp only [h2, ↓reduceIte]
        rw [hs, show s % 2 = 1 by omega, one_smul]; exact pointAdd_rep hq hp

/-- The encoding of an affine point (RFC 8032 §5.1.2). -/
def encodeAff (a : EPoint dZ) : List Byte :=
  Spec.Ed25519.encodeLE 32 (Fin.val (a.y : Fe) + (Fin.val (a.x : Fe) % 2) * 2 ^ 255)

theorem mul_pow_inv {z : ZMod P} (hz : z ≠ 0) (c : ZMod P) : c * z * z ^ (P - 2) = c := by
  rw [mul_assoc, ← pow_succ', show P - 2 + 1 = P - 1 by decide, ZMod.pow_card_sub_one_eq_one hz,
    mul_one]

theorem encodePoint_rep {p : Point} {a : EPoint dZ} (h : Rep p a) :
    Spec.Ed25519.encodePoint p = encodeAff a := by
  have hx : p.X * Spec.X25519.pow p.Z (P - 2) = (a.x : Fe) := by
    show toZ (p.X * Spec.X25519.pow p.Z (P - 2)) = a.x
    rw [toZ_mul, toZ_pow, h.x, mul_pow_inv h.z]
  have hy : p.Y * Spec.X25519.pow p.Z (P - 2) = (a.y : Fe) := by
    show toZ (p.Y * Spec.X25519.pow p.Z (P - 2)) = a.y
    rw [toZ_mul, toZ_pow, h.y, mul_pow_inv h.z]
  simp only [Spec.Ed25519.encodePoint, hx, hy, encodeAff]

theorem pointEqual_rep {p q : Point} {a b : EPoint dZ} (hp : Rep p a) (hq : Rep q b) :
    Spec.Ed25519.pointEqual p q = true ↔ a = b := by
  have hz : toZ p.Z * toZ q.Z ≠ 0 := mul_ne_zero hp.z hq.z
  simp only [Spec.Ed25519.pointEqual, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : toZ (p.X * q.Z) = toZ (q.X * p.Z) := congrArg toZ h1
    have e2 : toZ (p.Y * q.Z) = toZ (q.Y * p.Z) := congrArg toZ h2
    rw [toZ_mul, toZ_mul, hp.x, hq.x] at e1
    rw [toZ_mul, toZ_mul, hp.y, hq.y] at e2
    ext
    · exact mul_right_cancel₀ hz (by linear_combination e1)
    · exact mul_right_cancel₀ hz (by linear_combination e2)
  · rintro rfl
    refine ⟨toZ_inj.mp ?_, toZ_inj.mp ?_⟩
    · rw [toZ_mul, toZ_mul, hp.x, hq.x]; ring
    · rw [toZ_mul, toZ_mul, hp.y, hq.y]; ring

/-- The first of the projective comparisons: the `x` coordinates agree. -/
theorem rep_cross_x {p q : Point} {a b : EPoint dZ} (hp : Rep p a) (hq : Rep q b) :
    p.X * q.Z = q.X * p.Z ↔ a.x = b.x := by
  constructor
  · intro h
    have e : toZ (p.X * q.Z) = toZ (q.X * p.Z) := congrArg toZ h
    rw [toZ_mul, toZ_mul, hp.x, hq.x] at e
    exact mul_right_cancel₀ (mul_ne_zero hp.z hq.z) (by linear_combination e)
  · intro h
    exact toZ_inj.mp (by rw [toZ_mul, toZ_mul, hp.x, hq.x, h]; ring)

/-- The second: the `y` coordinates agree. -/
theorem rep_cross_y {p q : Point} {a b : EPoint dZ} (hp : Rep p a) (hq : Rep q b) :
    p.Y * q.Z = q.Y * p.Z ↔ a.y = b.y := by
  constructor
  · intro h
    have e : toZ (p.Y * q.Z) = toZ (q.Y * p.Z) := congrArg toZ h
    rw [toZ_mul, toZ_mul, hp.y, hq.y] at e
    exact mul_right_cancel₀ (mul_ne_zero hp.z hq.z) (by linear_combination e)
  · intro h
    exact toZ_inj.mp (by rw [toZ_mul, toZ_mul, hp.y, hq.y, h]; ring)

private theorem base_on : OnCurve dZ (toZ Spec.Ed25519.basePoint.X) (toZ Spec.Ed25519.basePoint.Y) := by
  unfold OnCurve dZ
  decide +kernel

/-- The base point `B` of RFC 8032 §5.1. -/
def baseAff : EPoint dZ := ⟨toZ Spec.Ed25519.basePoint.X, toZ Spec.Ed25519.basePoint.Y, base_on⟩

theorem basePoint_rep : Rep Spec.Ed25519.basePoint baseAff :=
  ⟨by decide, (mul_one _).symm, (mul_one _).symm, (mul_one _).symm⟩

/-- Another representative of the same point: the same projective `X : Y : Z`. -/
theorem Rep.of_proj {p q : Point} {a : EPoint dZ} (h : Rep p a) (hz : toZ q.Z ≠ 0)
    (hx : toZ q.X * toZ p.Z = toZ p.X * toZ q.Z) (hy : toZ q.Y * toZ p.Z = toZ p.Y * toZ q.Z)
    (ht : toZ q.T * toZ q.Z = toZ q.X * toZ q.Y) : Rep q a := by
  have ex : toZ q.X = a.x * toZ q.Z :=
    mul_right_cancel₀ h.z (by rw [hx, h.x]; ring)
  have ey : toZ q.Y = a.y * toZ q.Z :=
    mul_right_cancel₀ h.z (by rw [hy, h.y]; ring)
  exact ⟨hz, ex, ey, mul_right_cancel₀ hz (by rw [ht, ex, ey]; ring)⟩

/-- `(-X, Y, Z, -T)` represents `-a`. -/
def negPoint (p : Point) : Point := ⟨0 - p.X, p.Y, p.Z, 0 - p.T⟩

theorem Rep.neg {p : Point} {a : EPoint dZ} (h : Rep p a) : Rep (negPoint p) (-a) := by
  refine ⟨h.z, ?_, h.y, ?_⟩
  · show toZ (0 - p.X) = -a.x * toZ p.Z
    rw [toZ_sub, toZ_zero, h.x]; ring
  · show toZ (0 - p.T) = -a.x * a.y * toZ p.Z
    rw [toZ_sub, toZ_zero, h.t]; ring

theorem Rep.double {p : Point} {a : EPoint dZ} (h : Rep p a) :
    Rep (Spec.Ed25519.pointAdd p p) ((2 : Nat) • a) := by
  rw [two_nsmul]; exact pointAdd_rep h h

/-- An affine point with `Z = 1`. -/
theorem rep_affine (x y : Fe) (h : OnCurve dZ (toZ x) (toZ y)) :
    Rep ⟨x, y, 1, x * y⟩ ⟨toZ x, toZ y, h⟩ :=
  ⟨show toZ 1 ≠ 0 by decide, (mul_one _).symm, (mul_one _).symm, (mul_one _).symm⟩

end VG.Proof.Ed25519

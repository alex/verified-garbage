import VerifiedGarbage.Proof.Ed448.Group.Edwards
import VerifiedGarbage.Proof.Ed448.Group.Prime
import VerifiedGarbage.Spec.Ed448
import Mathlib.FieldTheory.Finite.Basic

/-!
# The specification's projective points represent points of the group

The specification's field `Fe = Fin P` is mapped into the field `ZMod PZ`
(`PZ = P`, irreducible: `Prime.lean`) by `toZ`, an injective ring homomorphism
(`toZ_add`, `toZ_mul`, …). Unlike for Ed25519, `toZ` is not the identity:
`ZMod P` unfolds to `Fin P` only by evaluating `P = 2^448 - 2^224 - 1`, whose
exponent the elaborator refuses to evaluate. For the same reason the
definitions that compute in `ZMod PZ` are `noncomputable` (the compiler would
evaluate `P`), and `Rep` is a conjunction rather than a `structure`. The
specification's `d` is not a square (its power `(P - 1) / 2` is `-1`), so the
Edwards addition law over `ZMod PZ` is complete (`params`).

`Rep p a`: the projective point `p` of the specification represents the
affine point `a`: `Z ≠ 0`, `X = xZ` and `Y = yZ`. Equivalently `Valid p`
(`Z ≠ 0` and `(X/Z, Y/Z)` is on the curve) and `toAffine p = a` (`rep_iff`).
The specification's addition, scalar multiplication, encoding and comparison
only depend on the points represented, which is what lets an implementation
compute other representatives of the same points. `double` is the doubling
formula of RFC 8032 §5.2.4.
-/

namespace VG.Proof.Ed448

open Spec.X448 (Fe P)
open Spec.Ed448 (Point)
open Edwards

/-! ## The field -/

/-- An element of `Fe` as an element of the field `ZMod PZ`. -/
noncomputable def toZ (a : Fe) : ZMod PZ := (a.val : ZMod PZ)

theorem natCast_mod_P (n : Nat) : ((n % P : Nat) : ZMod PZ) = n := by
  rw [show n % P = n % PZ by rw [PZ_eq], ZMod.natCast_mod]

theorem natCast_P : ((P : Nat) : ZMod PZ) = 0 := by
  rw [show P = PZ from PZ_eq.symm, ZMod.natCast_self]

theorem toZ_add (a b : Fe) : toZ (a + b) = toZ a + toZ b := by
  unfold toZ; rw [Fin.val_add, natCast_mod_P, Nat.cast_add]

theorem toZ_mul (a b : Fe) : toZ (a * b) = toZ a * toZ b := by
  unfold toZ; rw [Fin.val_mul, natCast_mod_P, Nat.cast_mul]

theorem toZ_sub (a b : Fe) : toZ (a - b) = toZ a - toZ b := by
  unfold toZ
  rw [Fin.val_sub, natCast_mod_P, Nat.cast_add, Nat.cast_sub b.isLt.le, natCast_P]
  ring

theorem toZ_zero : toZ 0 = 0 := by
  unfold toZ; rw [show (0 : Fe).val = 0 by decide +kernel, Nat.cast_zero]

theorem toZ_one : toZ 1 = 1 := by
  unfold toZ; rw [show (1 : Fe).val = 1 by decide +kernel, Nat.cast_one]

theorem toZ_inj {a b : Fe} : toZ a = toZ b ↔ a = b := by
  constructor
  · intro h
    have := (ZMod.natCast_eq_natCast_iff' a.val b.val PZ).mp h
    rw [PZ_eq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
    exact Fin.ext this
  · rintro rfl; rfl

theorem toZ_ne_zero {a : Fe} : toZ a ≠ 0 ↔ a ≠ 0 := by
  rw [← toZ_zero, Ne, toZ_inj]

theorem toZ_neg (a : Fe) : toZ (0 - a) = -toZ a := by
  rw [toZ_sub, toZ_zero, zero_sub]

theorem val_toZ (a : Fe) : (toZ a).val = a.val := by
  unfold toZ; rw [ZMod.val_natCast, PZ_eq, Nat.mod_eq_of_lt a.isLt]

theorem toZ_pow (a : Fe) (e : Nat) : toZ (Spec.X448.pow a e) = toZ a ^ e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [Spec.X448.pow]
    by_cases h0 : e = 0
    · subst h0; rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), toZ_one, pow_zero]
    · simp only [h0, ↓reduceIte]
      have hlt : e / 2 < e := Nat.div_lt_self (by omega) (by decide)
      have hsplit : toZ a ^ e = (toZ a * toZ a) ^ (e / 2) * toZ a ^ (e % 2) := by
        rw [← sq, ← pow_mul, ← pow_add]; congr 1; omega
      by_cases h2 : e % 2 = 0
      · simp only [h2, ↓reduceIte]
        rw [ih _ hlt, toZ_mul, hsplit, h2, pow_zero, mul_one]
      · simp only [h2, ↓reduceIte]
        rw [toZ_mul, ih _ hlt, toZ_mul, hsplit, show e % 2 = 1 by omega, pow_one, mul_comm]

/-- `z^(P-1) = 1` for `z ≠ 0` (Fermat). -/
theorem pow_P_sub_one {z : ZMod PZ} (hz : z ≠ 0) : z ^ (P - 1) = 1 := by
  rw [← PZ_eq]; exact ZMod.pow_card_sub_one_eq_one hz

/-! ## The curve's parameters -/

/-- The curve parameter `d` in `ZMod PZ`. -/
noncomputable def dZ : ZMod PZ := toZ Spec.Ed448.d

private theorem d_val : (Spec.Ed448.d : Fe).val = P - 39081 := by decide +kernel

private theorem d_pow : Pratt.powMod PZ 449 (P - 39081) ((P - 1) / 2) = PZ - 1 := by
  decide +kernel

theorem dZ_pow : dZ ^ ((P - 1) / 2) = -1 := by
  rw [dZ, toZ, d_val, ← Pratt.powMod_cast PZ 449 _ _ (by decide +kernel), d_pow,
    Nat.cast_sub (by decide +kernel), ZMod.natCast_self, Nat.cast_one, zero_sub]

theorem two_ne_zero' : (2 : ZMod PZ) ≠ 0 := by
  intro h
  have : ((2 : Nat) : ZMod PZ) = ((0 : Nat) : ZMod PZ) := by
    rw [Nat.cast_ofNat, Nat.cast_zero]; exact h
  rw [ZMod.natCast_eq_natCast_iff'] at this
  exact absurd this (by decide +kernel)

theorem dZ_ne_zero : dZ ≠ 0 := by
  intro h
  have := dZ_pow
  rw [h, zero_pow (by decide +kernel)] at this
  exact one_ne_zero (neg_eq_zero.mp this.symm)

/-- `d` is not a square in `ZMod PZ`. -/
theorem dZ_nonsq (r : ZMod PZ) : r ^ 2 ≠ dZ := by
  intro hr
  have hr0 : r ≠ 0 := by rintro rfl; apply dZ_ne_zero; rw [← hr]; ring
  have h2 := dZ_pow
  rw [← hr, ← pow_mul, show 2 * ((P - 1) / 2) = P - 1 by decide +kernel, pow_P_sub_one hr0] at h2
  exact two_ne_zero' (by linear_combination h2)

theorem params : Params dZ := ⟨two_ne_zero', dZ_nonsq⟩

instance fact_params : Fact (Params dZ) := ⟨params⟩

/-! ## Representatives -/

/-- `p` represents `a`: `Z ≠ 0`, `X = xZ` and `Y = yZ`. (Not a `structure`: the
code generated for one would evaluate `P`.) -/
abbrev Rep (p : Point) (a : EPoint dZ) : Prop :=
  toZ p.Z ≠ 0 ∧ toZ p.X = a.x * toZ p.Z ∧ toZ p.Y = a.y * toZ p.Z

theorem Rep.z {p : Point} {a : EPoint dZ} (h : Rep p a) : toZ p.Z ≠ 0 := h.1
theorem Rep.x {p : Point} {a : EPoint dZ} (h : Rep p a) : toZ p.X = a.x * toZ p.Z := h.2.1
theorem Rep.y {p : Point} {a : EPoint dZ} (h : Rep p a) : toZ p.Y = a.y * toZ p.Z := h.2.2

/-- `p` is a point of the curve: `Z ≠ 0` and `(X/Z, Y/Z)` is on it. -/
def Valid (p : Point) : Prop :=
  toZ p.Z ≠ 0 ∧ OnCurve dZ (toZ p.X / toZ p.Z) (toZ p.Y / toZ p.Z)

open Classical in
/-- The affine point `(X/Z, Y/Z)` of a valid point (and `0` otherwise). -/
noncomputable def toAffine (p : Point) : EPoint dZ :=
  if h : Valid p then ⟨toZ p.X / toZ p.Z, toZ p.Y / toZ p.Z, h.2⟩ else 0

section
variable {p q : Point} {a b : EPoint dZ}

theorem Rep.valid (h : Rep p a) : Valid p := by
  refine ⟨h.z, ?_⟩
  rw [h.x, h.y, mul_div_cancel_right₀ _ h.z, mul_div_cancel_right₀ _ h.z]
  exact a.on

theorem Rep.toAffine_eq (h : Rep p a) : toAffine p = a := by
  rw [toAffine, dite_eq_left_of_eq_true (eq_true h.valid)]
  ext
  · show toZ p.X / toZ p.Z = a.x
    rw [h.x, mul_div_cancel_right₀ _ h.z]
  · show toZ p.Y / toZ p.Z = a.y
    rw [h.y, mul_div_cancel_right₀ _ h.z]

theorem rep_toAffine (h : Valid p) : Rep p (toAffine p) := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [toAffine, dite_eq_left_of_eq_true (eq_true h)]; exact (div_mul_cancel₀ _ h.1).symm
  · rw [toAffine, dite_eq_left_of_eq_true (eq_true h)]; exact (div_mul_cancel₀ _ h.1).symm

theorem rep_iff : Rep p a ↔ Valid p ∧ toAffine p = a :=
  ⟨fun h => ⟨h.valid, h.toAffine_eq⟩, fun ⟨h, e⟩ => e ▸ rep_toAffine h⟩

theorem Rep.unique (h : Rep p a) (h' : Rep p b) : a = b :=
  h.toAffine_eq.symm.trans h'.toAffine_eq

/-- Another representative of the same point: the same projective `X : Y : Z`. -/
theorem Rep.of_proj (h : Rep p a) (hz : toZ q.Z ≠ 0)
    (hx : toZ q.X * toZ p.Z = toZ p.X * toZ q.Z) (hy : toZ q.Y * toZ p.Z = toZ p.Y * toZ q.Z) :
    Rep q a :=
  ⟨hz, mul_right_cancel₀ h.z (by rw [hx, h.x]; ring),
    mul_right_cancel₀ h.z (by rw [hy, h.y]; ring)⟩

/-- An affine point with `Z = 1`. -/
theorem rep_affine (x y : Fe) (h : OnCurve dZ (toZ x) (toZ y)) :
    Rep ⟨x, y, 1⟩ ⟨toZ x, toZ y, h⟩ :=
  ⟨by rw [toZ_one]; exact one_ne_zero, by rw [toZ_one, mul_one], by rw [toZ_one, mul_one]⟩

/-! ## Scaling and negation -/

/-- `⟨λX, λY, λZ⟩`. -/
def scale (l : Fe) (p : Point) : Point := ⟨l * p.X, l * p.Y, l * p.Z⟩

theorem Rep.scale {l : Fe} (h : Rep p a) (hl : l ≠ 0) : Rep (scale l p) a := by
  refine ⟨?_, ?_, ?_⟩
  · show toZ (l * p.Z) ≠ 0
    rw [toZ_mul]; exact mul_ne_zero (toZ_ne_zero.mpr hl) h.z
  · show toZ (l * p.X) = a.x * toZ (l * p.Z)
    rw [toZ_mul, toZ_mul, h.x]; ring
  · show toZ (l * p.Y) = a.y * toZ (l * p.Z)
    rw [toZ_mul, toZ_mul, h.y]; ring

theorem valid_scale {l : Fe} (h : Valid p) (hl : l ≠ 0) : Valid (scale l p) :=
  ((rep_toAffine h).scale hl).valid

theorem toAffine_scale {l : Fe} (h : Valid p) (hl : l ≠ 0) : toAffine (scale l p) = toAffine p :=
  ((rep_toAffine h).scale hl).toAffine_eq

/-- `⟨-X, Y, Z⟩`. -/
def negPoint (p : Point) : Point := ⟨0 - p.X, p.Y, p.Z⟩

theorem Rep.neg (h : Rep p a) : Rep (negPoint p) (-a) := by
  refine ⟨h.z, ?_, h.y⟩
  show toZ (0 - p.X) = -a.x * toZ p.Z
  rw [toZ_neg, h.x]; ring

theorem valid_negPoint (h : Valid p) : Valid (negPoint p) := (rep_toAffine h).neg.valid

theorem toAffine_negPoint (h : Valid p) : toAffine (negPoint p) = -toAffine p :=
  (rep_toAffine h).neg.toAffine_eq

end

/-! ## The identity and the base point -/

theorem identity_rep : Rep Spec.Ed448.identity 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show toZ 1 ≠ 0
    rw [toZ_one]; exact one_ne_zero
  · show toZ 0 = 0 * toZ 1
    rw [toZ_zero, zero_mul]
  · show toZ 1 = 1 * toZ 1
    rw [one_mul]

theorem identity_valid : Valid Spec.Ed448.identity := identity_rep.valid

theorem toAffine_identity : toAffine Spec.Ed448.identity = 0 := identity_rep.toAffine_eq

private theorem base_fe :
    Spec.Ed448.basePoint.X * Spec.Ed448.basePoint.X + Spec.Ed448.basePoint.Y * Spec.Ed448.basePoint.Y =
      1 + Spec.Ed448.d * Spec.Ed448.basePoint.X * Spec.Ed448.basePoint.X *
        Spec.Ed448.basePoint.Y * Spec.Ed448.basePoint.Y := by
  decide +kernel

private theorem base_on :
    OnCurve dZ (toZ Spec.Ed448.basePoint.X) (toZ Spec.Ed448.basePoint.Y) := by
  have e := congrArg toZ base_fe
  simp only [toZ_add, toZ_mul, toZ_one] at e
  unfold OnCurve dZ
  linear_combination e

/-- The base point `B` of RFC 8032 §5.2. -/
noncomputable def baseAff : EPoint dZ := ⟨toZ Spec.Ed448.basePoint.X, toZ Spec.Ed448.basePoint.Y, base_on⟩

private theorem base_z : Spec.Ed448.basePoint.Z = 1 := rfl

theorem basePoint_rep : Rep Spec.Ed448.basePoint baseAff := by
  refine ⟨?_, ?_, ?_⟩
  · rw [base_z, toZ_one]; exact one_ne_zero
  · rw [base_z, toZ_one, mul_one]; rfl
  · rw [base_z, toZ_one, mul_one]; rfl

theorem basePoint_valid : Valid Spec.Ed448.basePoint := basePoint_rep.valid

theorem toAffine_basePoint : toAffine Spec.Ed448.basePoint = baseAff := basePoint_rep.toAffine_eq

/-! ## Addition and scalar multiplication -/

section
variable (p q : Point)

theorem pointAdd_X : toZ (Spec.Ed448.pointAdd p q).X =
    toZ p.Z * toZ q.Z * (toZ p.Z * toZ q.Z * (toZ p.Z * toZ q.Z) -
      dZ * (toZ p.X * toZ q.X) * (toZ p.Y * toZ q.Y)) *
      ((toZ p.X + toZ p.Y) * (toZ q.X + toZ q.Y) - toZ p.X * toZ q.X - toZ p.Y * toZ q.Y) := by
  simp only [Spec.Ed448.pointAdd, toZ_mul, toZ_add, toZ_sub, dZ]

theorem pointAdd_Y : toZ (Spec.Ed448.pointAdd p q).Y =
    toZ p.Z * toZ q.Z * (toZ p.Z * toZ q.Z * (toZ p.Z * toZ q.Z) +
      dZ * (toZ p.X * toZ q.X) * (toZ p.Y * toZ q.Y)) *
      (toZ p.Y * toZ q.Y - toZ p.X * toZ q.X) := by
  simp only [Spec.Ed448.pointAdd, toZ_mul, toZ_add, toZ_sub, dZ]

theorem pointAdd_Z : toZ (Spec.Ed448.pointAdd p q).Z =
    (toZ p.Z * toZ q.Z * (toZ p.Z * toZ q.Z) - dZ * (toZ p.X * toZ q.X) * (toZ p.Y * toZ q.Y)) *
      (toZ p.Z * toZ q.Z * (toZ p.Z * toZ q.Z) + dZ * (toZ p.X * toZ q.X) * (toZ p.Y * toZ q.Y)) := by
  simp only [Spec.Ed448.pointAdd, toZ_mul, toZ_add, toZ_sub, dZ]

end

theorem pointAdd_rep {p q : Point} {a b : EPoint dZ} (hp : Rep p a) (hq : Rep q b) :
    Rep (Spec.Ed448.pointAdd p q) (a + b) := by
  have ha := den_add_ne params a.on b.on
  have hs := den_sub_ne params a.on b.on
  have hu := mul_inv_cancel₀ ha
  have hv := mul_inv_cancel₀ hs
  have hZ : toZ (Spec.Ed448.pointAdd p q).Z = (toZ p.Z * toZ q.Z) ^ 4 *
      (1 - dZ * a.x * b.x * a.y * b.y) * (1 + dZ * a.x * b.x * a.y * b.y) := by
    rw [pointAdd_Z, hp.x, hp.y, hq.x, hq.y]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hZ]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 4 (mul_ne_zero hp.z hq.z)) hs) ha
  · rw [hZ, pointAdd_X, hp.x, hp.y, hq.x, hq.y, add_x, addX, div_eq_mul_inv]
    linear_combination (-((toZ p.Z * toZ q.Z) ^ 4 * (a.x * b.y + a.y * b.x) *
      (1 - dZ * a.x * b.x * a.y * b.y))) * hu
  · rw [hZ, pointAdd_Y, hp.x, hp.y, hq.x, hq.y, add_y, addY, div_eq_mul_inv]
    linear_combination (-((toZ p.Z * toZ q.Z) ^ 4 * (a.y * b.y - a.x * b.x) *
      (1 + dZ * a.x * b.x * a.y * b.y))) * hv

theorem pointAdd_valid {p q : Point} (hp : Valid p) (hq : Valid q) :
    Valid (Spec.Ed448.pointAdd p q) :=
  (pointAdd_rep (rep_toAffine hp) (rep_toAffine hq)).valid

theorem toAffine_pointAdd {p q : Point} (hp : Valid p) (hq : Valid q) :
    toAffine (Spec.Ed448.pointAdd p q) = toAffine p + toAffine q :=
  (pointAdd_rep (rep_toAffine hp) (rep_toAffine hq)).toAffine_eq

theorem pointMul_rep (s : Nat) : ∀ {p : Point} {a : EPoint dZ}, Rep p a →
    Rep (Spec.Ed448.pointMul s p) (s • a) := by
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro p a hp
    rw [Spec.Ed448.pointMul]
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

theorem pointMul_valid (s : Nat) {p : Point} (hp : Valid p) : Valid (Spec.Ed448.pointMul s p) :=
  (pointMul_rep s (rep_toAffine hp)).valid

theorem toAffine_pointMul (s : Nat) {p : Point} (hp : Valid p) :
    toAffine (Spec.Ed448.pointMul s p) = s • toAffine p :=
  (pointMul_rep s (rep_toAffine hp)).toAffine_eq

/-! ## Doubling (RFC 8032 §5.2.4) -/

/-- `B = (X+Y)²`, `C = X²`, `D = Y²`, `E = C+D`, `H = Z²`, `J = E-2H`, and
`((B-E)J, E(C-D), EJ)`. -/
def double (p : Point) : Point :=
  let b := (p.X + p.Y) * (p.X + p.Y)
  let c := p.X * p.X
  let dd := p.Y * p.Y
  let e := c + dd
  let h := p.Z * p.Z
  let j := e - (h + h)
  ⟨(b - e) * j, e * (c - dd), e * j⟩

section
variable (p : Point)

theorem double_X : (double p).X = ((p.X + p.Y) * (p.X + p.Y) - (p.X * p.X + p.Y * p.Y)) *
    (p.X * p.X + p.Y * p.Y - (p.Z * p.Z + p.Z * p.Z)) := rfl

theorem double_Y : (double p).Y = (p.X * p.X + p.Y * p.Y) * (p.X * p.X - p.Y * p.Y) := rfl

theorem double_Z : (double p).Z = (p.X * p.X + p.Y * p.Y) *
    (p.X * p.X + p.Y * p.Y - (p.Z * p.Z + p.Z * p.Z)) := rfl

end

theorem double_rep {p : Point} {a : EPoint dZ} (h : Rep p a) : Rep (double p) (a + a) := by
  have hon : a.x ^ 2 + a.y ^ 2 = 1 + dZ * a.x ^ 2 * a.y ^ 2 := a.on
  have ha := den_add_ne params a.on a.on
  have hs := den_sub_ne params a.on a.on
  have hu := mul_inv_cancel₀ ha
  have hv := mul_inv_cancel₀ hs
  have hE : toZ (p.X * p.X + p.Y * p.Y) = toZ p.Z ^ 2 * (1 + dZ * a.x * a.x * a.y * a.y) := by
    rw [toZ_add, toZ_mul, toZ_mul, h.x, h.y]
    linear_combination toZ p.Z ^ 2 * hon
  have hBE : toZ ((p.X + p.Y) * (p.X + p.Y) - (p.X * p.X + p.Y * p.Y)) =
      2 * a.x * a.y * toZ p.Z ^ 2 := by
    simp only [toZ_sub, toZ_mul, toZ_add, h.x, h.y]; ring
  have hJ : toZ (p.X * p.X + p.Y * p.Y - (p.Z * p.Z + p.Z * p.Z)) =
      -(toZ p.Z ^ 2 * (1 - dZ * a.x * a.x * a.y * a.y)) := by
    rw [toZ_sub, hE, toZ_add, toZ_mul]; ring
  have hCD : toZ (p.X * p.X - p.Y * p.Y) = (a.x ^ 2 - a.y ^ 2) * toZ p.Z ^ 2 := by
    simp only [toZ_sub, toZ_mul, h.x, h.y]; ring
  have hZ : toZ (double p).Z = toZ p.Z ^ 2 * (1 + dZ * a.x * a.x * a.y * a.y) *
      -(toZ p.Z ^ 2 * (1 - dZ * a.x * a.x * a.y * a.y)) := by
    rw [double_Z, toZ_mul, hE, hJ]
  refine ⟨?_, ?_, ?_⟩
  · rw [hZ]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h.z) ha)
      (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 h.z) hs))
  · rw [hZ, double_X, toZ_mul, hBE, hJ, add_x, addX, div_eq_mul_inv]
    linear_combination (2 * a.x * a.y * toZ p.Z ^ 4 * (1 - dZ * a.x * a.x * a.y * a.y)) * hu
  · rw [hZ, double_Y, toZ_mul, hE, hCD, add_y, addY, div_eq_mul_inv]
    linear_combination (-(toZ p.Z ^ 4 * (1 + dZ * a.x * a.x * a.y * a.y) * (a.x ^ 2 - a.y ^ 2))) * hv

theorem double_valid {p : Point} (hp : Valid p) : Valid (double p) :=
  (double_rep (rep_toAffine hp)).valid

theorem toAffine_double {p : Point} (hp : Valid p) : toAffine (double p) = toAffine p + toAffine p :=
  (double_rep (rep_toAffine hp)).toAffine_eq

/-! ## Comparison and encoding -/

theorem pointEqual_rep {p q : Point} {a b : EPoint dZ} (hp : Rep p a) (hq : Rep q b) :
    Spec.Ed448.pointEqual p q = true ↔ a = b := by
  have hz : toZ p.Z * toZ q.Z ≠ 0 := mul_ne_zero hp.z hq.z
  simp only [Spec.Ed448.pointEqual, Bool.and_eq_true, beq_iff_eq]
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

theorem pointEqual_iff {p q : Point} (hp : Valid p) (hq : Valid q) :
    Spec.Ed448.pointEqual p q = true ↔ toAffine p = toAffine q :=
  pointEqual_rep (rep_toAffine hp) (rep_toAffine hq)

/-- The encoding only depends on the affine coordinates `X/Z`, `Y/Z`. -/
theorem encodePoint_congr {p q : Point}
    (hx : p.X * Spec.X448.pow p.Z (P - 2) = q.X * Spec.X448.pow q.Z (P - 2))
    (hy : p.Y * Spec.X448.pow p.Z (P - 2) = q.Y * Spec.X448.pow q.Z (P - 2)) :
    Spec.Ed448.encodePoint p = Spec.Ed448.encodePoint q := by
  unfold Spec.Ed448.encodePoint
  dsimp only [-Nat.reducePow]
  rw [hx, hy]

/-- An element of `ZMod PZ` as an element of `Fe`. -/
noncomputable def ofZ (z : ZMod PZ) : Fe := ⟨z.val, by rw [← PZ_eq]; exact ZMod.val_lt z⟩

theorem toZ_ofZ (z : ZMod PZ) : toZ (ofZ z) = z := ZMod.natCast_zmod_val z

theorem ofZ_toZ (a : Fe) : ofZ (toZ a) = a := Fin.ext (val_toZ a)

/-- The encoding of an affine point (RFC 8032 §5.2.2): that of `(x, y, 1)`. -/
noncomputable def encodeAff (a : EPoint dZ) : List Byte := Spec.Ed448.encodePoint ⟨ofZ a.x, ofZ a.y, 1⟩

theorem mul_pow_inv {z : ZMod PZ} (hz : z ≠ 0) (c : ZMod PZ) : c * z * z ^ (P - 2) = c := by
  rw [mul_assoc, ← pow_succ', show P - 2 + 1 = P - 1 by decide +kernel, pow_P_sub_one hz,
    mul_one]

theorem encodePoint_rep {p : Point} {a : EPoint dZ} (h : Rep p a) :
    Spec.Ed448.encodePoint p = encodeAff a := by
  refine encodePoint_congr (toZ_inj.mp ?_) (toZ_inj.mp ?_)
  · rw [toZ_mul, toZ_pow, h.x, mul_pow_inv h.z, toZ_mul, toZ_pow, toZ_ofZ, toZ_one, one_pow,
      mul_one]
  · rw [toZ_mul, toZ_pow, h.y, mul_pow_inv h.z, toZ_mul, toZ_pow, toZ_ofZ, toZ_one, one_pow,
      mul_one]

theorem encodePoint_eq {p q : Point} (hp : Valid p) (hq : Valid q)
    (h : toAffine p = toAffine q) : Spec.Ed448.encodePoint p = Spec.Ed448.encodePoint q := by
  rw [encodePoint_rep (rep_toAffine hp), encodePoint_rep (rep_toAffine hq), h]

end VG.Proof.Ed448

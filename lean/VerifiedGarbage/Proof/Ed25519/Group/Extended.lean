import VerifiedGarbage.Proof.Ed25519.Group.Field
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Group.Basic

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

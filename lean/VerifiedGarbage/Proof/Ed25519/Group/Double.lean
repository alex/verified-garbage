import VerifiedGarbage.Proof.Ed25519.Group.Extended

/-!
# Doubling with the dedicated formula

Untrusted. `dblPoint` is the doubling `dbl-2008-hwcd` of Hisil, Wong, Carter
and Dawson for `a = -1`, with the signs of `F` and `H` flipped, which scales
the result by `-1` (the same point). It reads only `X : Y : Z` (`RepP`), so a
chain of doublings need not compute `T` but at its end.
-/

namespace VG.Proof.Ed25519

open Spec.X25519 (Fe P)
open Spec.Ed25519 (Point)
open Edwards

/-- `p`'s `X : Y : Z` represent `a`; its `T` may be anything. -/
structure RepP (p : Point) (a : EPoint dZ) : Prop where
  z : toZ p.Z ≠ 0
  x : toZ p.X = a.x * toZ p.Z
  y : toZ p.Y = a.y * toZ p.Z

theorem Rep.proj {p : Point} {a : EPoint dZ} (h : Rep p a) : RepP p a := ⟨h.z, h.x, h.y⟩

/-- `E = 2XY`, `G = Y² - X²`, `F = 2Z² - G`, `H = X² + Y²`, and
`(EF, GH, FG, EH)`. -/
def dblPoint (p : Point) : Point :=
  ⟨(p.X * p.Y + p.X * p.Y) * (p.Z * p.Z + p.Z * p.Z - (p.Y * p.Y - p.X * p.X)),
    (p.Y * p.Y - p.X * p.X) * (p.X * p.X + p.Y * p.Y),
    (p.Z * p.Z + p.Z * p.Z - (p.Y * p.Y - p.X * p.X)) * (p.Y * p.Y - p.X * p.X),
    (p.X * p.Y + p.X * p.Y) * (p.X * p.X + p.Y * p.Y)⟩

theorem dblPoint_rep {p : Point} {a : EPoint dZ} (h : RepP p a) : Rep (dblPoint p) (a + a) := by
  have hon : -a.x ^ 2 + a.y ^ 2 = 1 + dZ * a.x ^ 2 * a.y ^ 2 := a.on
  have ha := den_add_ne params a.on a.on
  have hs := den_sub_ne params a.on a.on
  have hu := mul_inv_cancel₀ ha
  have hv := mul_inv_cancel₀ hs
  have hE : toZ (p.X * p.Y + p.X * p.Y) = 2 * a.x * a.y * toZ p.Z ^ 2 := by
    rw [toZ_add, toZ_mul, h.x, h.y]; ring
  have hG : toZ (p.Y * p.Y - p.X * p.X) =
      toZ p.Z ^ 2 * (1 + dZ * a.x * a.x * a.y * a.y) := by
    rw [toZ_sub, toZ_mul, toZ_mul, h.x, h.y]
    linear_combination toZ p.Z ^ 2 * hon
  have hF : toZ (p.Z * p.Z + p.Z * p.Z - (p.Y * p.Y - p.X * p.X)) =
      toZ p.Z ^ 2 * (1 - dZ * a.x * a.x * a.y * a.y) := by
    rw [toZ_sub, hG, toZ_add, toZ_mul]; ring
  have hH : toZ (p.X * p.X + p.Y * p.Y) = toZ p.Z ^ 2 * (a.x ^ 2 + a.y ^ 2) := by
    rw [toZ_add, toZ_mul, toZ_mul, h.x, h.y]; ring
  have hZ : toZ (dblPoint p).Z = toZ p.Z ^ 2 * (1 - dZ * a.x * a.x * a.y * a.y) *
      (toZ p.Z ^ 2 * (1 + dZ * a.x * a.x * a.y * a.y)) := by
    show toZ (_ * _) = _
    rw [toZ_mul, hF, hG]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hZ]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h.z) hs) (mul_ne_zero (pow_ne_zero 2 h.z) ha)
  · rw [hZ, show (dblPoint p).X = _ * _ from rfl, toZ_mul, hE, hF, add_x, addX, div_eq_mul_inv]
    linear_combination (-(2 * a.x * a.y * toZ p.Z ^ 4 * (1 - dZ * a.x * a.x * a.y * a.y))) * hu
  · rw [hZ, show (dblPoint p).Y = _ * _ from rfl, toZ_mul, hG, hH, add_y, addY, div_eq_mul_inv]
    linear_combination (-(toZ p.Z ^ 4 * (1 + dZ * a.x * a.x * a.y * a.y) * (a.x ^ 2 + a.y ^ 2))) * hv
  · rw [hZ, show (dblPoint p).T = _ * _ from rfl, toZ_mul, hE, hH, add_x, add_y, addX, addY,
      div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-(2 * a.x * a.y * (a.x ^ 2 + a.y ^ 2) * toZ p.Z ^ 4)) * hu +
      (-(2 * a.x * a.y * (a.x ^ 2 + a.y ^ 2) * toZ p.Z ^ 4 *
        (1 + dZ * a.x * a.x * a.y * a.y)⁻¹ * (1 + dZ * a.x * a.x * a.y * a.y))) * hv

end VG.Proof.Ed25519

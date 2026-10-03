import VerifiedGarbage.Proof.Weierstrass.Complete
import VerifiedGarbage.Spec.EcKey

/-!
# Public keys from a projective representative

`publicKey_eq`: given a representative `(X : Y : Z)` over `Fin p` of `[d]G`
and numbers
`x, y < p` with `x = X Z^(p-2)` and `y = Y Z^(p-2)`, the specification's
public key of `d` is `(x, y)` if `d` is in `[1, n-1]` and `Z ≠ 0`, `O` if
`d` is and `Z = 0`, and none otherwise.
-/

namespace VG.Proof.EcKey

open Spec.Weierstrass Spec.EcKey VG.Proof.Weierstrass

variable {C : Curve}

theorem fe_eq {x : Nat} (hx : x < C.p) {a : Fe C} (h : a = Fin.ofNat C.p x) : a = ⟨x, hx⟩ := by
  rw [h]
  exact Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt hx])

/-- The affine point a representative with `Z ≠ 0` stands for. -/
theorem affine_of_rep (hC : Good C) {X Y Z : Fe C} {P : Point C} (hR : Rep C X Y Z P) (hZ : Z ≠ 0)
    {x y : Nat} (hx : x < C.p) (hxX : Fin.ofNat C.p x = X * Z ^ (C.p - 2))
    (hy : y < C.p) (hyY : Fin.ofNat C.p y = Y * Z ^ (C.p - 2)) :
    P = .affine ⟨x, hx⟩ ⟨y, hy⟩ := by
  cases P with
  | infinity => exact absurd (hR.z_eq_zero_iff.mpr rfl) hZ
  | affine a b =>
    rw [fe_eq hx ((hR.x_eq hC).trans hxX.symm), fe_eq hy ((hR.y_eq hC).trans hyY.symm)]

theorem publicKey_eq (hC : Good C) {d : Nat} {X Y Z : Fe C} (hR : Rep C X Y Z (mul d (G C)))
    {x y : Nat} (hx : x < C.p) (hxX : Fin.ofNat C.p x = X * Z ^ (C.p - 2))
    (hy : y < C.p) (hyY : Fin.ofNat C.p y = Y * Z ^ (C.p - 2)) :
    publicKey C d = if 1 ≤ d ∧ d < C.n then
      (if Z = 0 then some .infinity else some (.affine ⟨x, hx⟩ ⟨y, hy⟩)) else none := by
  unfold publicKey
  by_cases hd : 1 ≤ d ∧ d < C.n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd), ite_eq_left_of_eq_true _ _ (eq_true hd)]
    by_cases hZ : Z = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hZ), hR.z_eq_zero_iff.mp hZ]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hZ), affine_of_rep hC hR hZ hx hxX hy hyY]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hd), ite_eq_right_of_eq_false _ _ (eq_false hd)]

end VG.Proof.EcKey

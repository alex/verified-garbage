import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Spec.Ecdh

/-!
# ECDH from a projective representative

`exchange_eq`: the specification's shared secret of `d` and the octet
string `bs` (`04 ‖ x ‖ y`), from a representative `(X : Y : Z)` of `[d]P`
and a number `xo < p` with `xo = X Z^(p-2)`, where `P` is the peer's point
whenever the peer's public key is valid (`V`): it is `xo` if `d` is in
`[1, n-1]`, the key is valid and `Z ≠ 0`, and none otherwise. The validity
of the key is stated as the code checks it: the first octet is `04`, both
coordinates are below `p`, and `y² - (x³ + a x + b) = 0` in `Fin p`
(`onCurve_iff`).
-/

namespace VG.Proof.Ecdh

open Spec.Weierstrass Spec.EcKey VG.Proof.Weierstrass VG.Proof.EcKey

variable {C : Curve}

/-- The curve's equation, in `Fin p`. -/
abbrev OnCurveF (C : Curve) (x y : Nat) : Prop :=
  Fin.ofNat C.p y * Fin.ofNat C.p y - ((Fin.ofNat C.p x * Fin.ofNat C.p x * Fin.ofNat C.p x +
    Fin.ofNat C.p C.a * Fin.ofNat C.p x) + Fin.ofNat C.p C.b) = 0

theorem onCurve_iff {x y : Nat} (hx : x < C.p) (hy : y < C.p) :
    onCurve C (.affine ⟨x, hx⟩ ⟨y, hy⟩) = true ↔ OnCurveF C x y := by
  have ex : (⟨x, hx⟩ : Fe C) = Fin.ofNat C.p x := (fe_eq hx rfl).symm
  have ey : (⟨y, hy⟩ : Fe C) = Fin.ofNat C.p y := (fe_eq hy rfl).symm
  rw [onCurve, decide_eq_true_iff, ex, ey]
  constructor <;> intro h <;> grind

/-- The peer's key, as the code checks it. -/
def Valid (C : Curve) (b0 : Byte) (x y : Nat) : Prop :=
  b0 = 4 ∧ x < C.p ∧ y < C.p ∧ OnCurveF C x y

instance (b0 : Byte) (x y : Nat) : Decidable (Valid C b0 x y) := by
  unfold Valid; infer_instance

theorem decode_eq {bs : List Byte} (hlen : bs.length = 2 * C.len + 1) {b0 : Byte}
    (hb0 : bs.head? = some b0) {x y : Nat} (hxv : ofBytes ((bs.drop 1).take C.len) = x)
    (hyv : ofBytes (bs.drop (C.len + 1)) = y) :
    decodePublicKey C bs =
      if h : Valid C b0 x y then some (.affine ⟨x, h.2.1⟩ ⟨y, h.2.2.1⟩) else none := by
  unfold decodePublicKey
  simp only [hlen, hb0, true_and, Option.some.injEq, hxv, hyv]
  by_cases h4 : b0 = 4
  · subst h4
    by_cases hxy : x < C.p ∧ y < C.p
    · by_cases hc : OnCurveF C x y
      · have hV : Valid C 4 x y := ⟨rfl, hxy.1, hxy.2, hc⟩
        simp only [hxy, (onCurve_iff hxy.1 hxy.2).mpr hc, hV, dite_true, ite_true, and_self]
      · have hV : ¬ Valid C 4 x y := fun h => hc h.2.2.2
        have hc' : onCurve C (.affine ⟨x, hxy.1⟩ ⟨y, hxy.2⟩) = false := by
          rw [← Bool.not_eq_true, onCurve_iff]; exact hc
        simp only [hxy, hc', hV, dite_true, dite_false, ite_true, and_self, Bool.false_eq_true,
          ite_false]
    · have hV : ¬ Valid C 4 x y := fun h => hxy ⟨h.2.1, h.2.2.1⟩
      simp only [hxy, hV, dite_false, ite_true]
  · have hV : ¬ Valid C b0 x y := fun h => h4 h.1
    simp only [h4, hV, dite_false, ite_false]

theorem exchange_eq (hC : Good C) {d : Nat} {bs : List Byte} (hlen : bs.length = 2 * C.len + 1) {b0 : Byte}
    (hb0 : bs.head? = some b0) {x y : Nat} (hxv : ofBytes ((bs.drop 1).take C.len) = x)
    (hyv : ofBytes (bs.drop (C.len + 1)) = y) {P : Point C}
    (hP : ∀ h : Valid C b0 x y, P = .affine ⟨x, h.2.1⟩ ⟨y, h.2.2.1⟩)
    {X Y Z : Fe C} (hR : Rep C X Y Z (mul d P)) {xo : Nat} (hxo : xo < C.p)
    (hxoX : Fin.ofNat C.p xo = X * Z ^ (C.p - 2)) :
    Spec.Ecdh.exchange C d bs =
      if (1 ≤ d ∧ d < C.n) ∧ Valid C b0 x y ∧ Z ≠ 0 then some (toBytes C.len xo) else none := by
  unfold Spec.Ecdh.exchange
  rw [decode_eq hlen hb0 hxv hyv]
  by_cases hd : 1 ≤ d ∧ d < C.n
  · by_cases hV : Valid C b0 x y
    · simp only [hd, hV, and_self, ite_true, dite_true, true_and]
      rw [← hP hV]
      by_cases hZ : Z = 0
      · rw [hR.z_eq_zero_iff.mp hZ]
        simp only [ne_eq, hZ, not_true_eq_false, ite_false]
      · simp only [ne_eq, hZ, not_false_eq_true, ite_true]
        generalize hQ : mul d P = Q at hR
        cases Q with
        | infinity => exact absurd (hR.z_eq_zero_iff.mpr rfl) hZ
        | affine a b => rw [fe_eq hxo ((hR.x_eq hC).trans hxoX.symm)]
    · simp only [hd, hV, and_self, ite_true, dite_false, false_and, and_false, ite_false]
  · simp only [hd, false_and, ite_false]

end VG.Proof.Ecdh

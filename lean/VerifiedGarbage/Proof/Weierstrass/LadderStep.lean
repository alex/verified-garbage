import VerifiedGarbage.Proof.Weierstrass.Complete
import VerifiedGarbage.Proof.Weierstrass.Ladder

/-!
# An iteration of the ladder on projective representatives

From a representative of `[k >>> (j + 1)]P`, the complete addition gives
representatives of `D = R + R` and `T = D + P`, and selecting `T` if bit `j`
of `k` is set, else `D`, represents `[k >>> j]P` (`ladder_step`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

theorem ladder_step (hC : Good C) {P : Point C} (hP : onCurve C P = true) {k j : Nat}
    {Px Py Pz X Y Z X2 Y2 Z2 X3 Y3 Z3 : ZMod C.p}
    (hPr : Rep C Px Py Pz P) (hR : Rep C X Y Z (mul (k >>> (j + 1)) P))
    (h2 : rcbAdd (C.a : ZMod C.p) (3 * (C.b : ZMod C.p)) X Y Z X Y Z = (X2, Y2, Z2))
    (h3 : rcbAdd (C.a : ZMod C.p) (3 * (C.b : ZMod C.p)) X2 Y2 Z2 Px Py Pz = (X3, Y3, Z3)) :
    Rep C (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2) (mul (k >>> j) P) := by
  have hm := hC.onCurve_mul hP (k >>> (j + 1))
  have hD := rcbAdd_rep hC hm hm hR hR h2
  have hDc := hC.onCurve_add hm hm
  have hT := rcbAdd_rep hC hDc hP hD hPr h3
  rw [mul_shiftRight P k j]
  by_cases hb : k.testBit j <;> simp only [hb, ite_true, ite_false, Bool.false_eq_true]
  · exact hT
  · exact hD

end VG.Proof.Weierstrass

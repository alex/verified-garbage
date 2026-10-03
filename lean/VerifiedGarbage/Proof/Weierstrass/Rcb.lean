import Mathlib.Algebra.Ring.Defs

/-!
# Complete projective addition (Renes, Costello and Batina)

Algorithm 1 of Renes, Costello and Batina, "Complete addition formulas for
prime order elliptic curves" (EUROCRYPT 2016): the sum of two points
`(X₁ : Y₁ : Z₁)` and `(X₂ : Y₂ : Z₂)` of `Y²Z = X³ + aXZ² + bZ³`, for any
`a`, with `b3 = 3b`, in its 40 steps, as the implementations compute it.
-/

namespace VG.Proof.Weierstrass

variable {F : Type*} [CommRing F]

/-- Algorithm 1, in its stated order. -/
def rcbAdd (a b3 X1 Y1 Z1 X2 Y2 Z2 : F) : F × F × F :=
  let t0 := X1 * X2
  let t1 := Y1 * Y2
  let t2 := Z1 * Z2
  let t3 := X1 + Y1
  let t4 := X2 + Y2
  let t3 := t3 * t4
  let t4 := t0 + t1
  let t3 := t3 - t4
  let t4 := X1 + Z1
  let t5 := X2 + Z2
  let t4 := t4 * t5
  let t5 := t0 + t2
  let t4 := t4 - t5
  let t5 := Y1 + Z1
  let X3 := Y2 + Z2
  let t5 := t5 * X3
  let X3 := t1 + t2
  let t5 := t5 - X3
  let Z3 := a * t4
  let X3 := b3 * t2
  let Z3 := X3 + Z3
  let X3 := t1 - Z3
  let Z3 := t1 + Z3
  let Y3 := X3 * Z3
  let t1 := t0 + t0
  let t1 := t1 + t0
  let t2 := a * t2
  let t4 := b3 * t4
  let t1 := t1 + t2
  let t2 := t0 - t2
  let t2 := a * t2
  let t4 := t4 + t2
  let t0 := t1 * t4
  let Y3 := Y3 + t0
  let t0 := t5 * t4
  let X3 := t3 * X3
  let X3 := X3 - t0
  let t0 := t3 * t1
  let Z3 := t5 * Z3
  let Z3 := Z3 + t0
  (X3, Y3, Z3)

end VG.Proof.Weierstrass

import VerifiedGarbage.Proof.X448.Invert

/-!
# Ed448: the square-root exponent `(p-3)/4` as an addition chain

`x^((p-3)/4)`, which decoding raises `u⁵v³` to (RFC 8032 §5.2.3), shares
X448's addition chain for the inversion as far as `x^(2²²³ - 1)`, and
`(p-3)/4 = 2²⁴⁶ - 2²²² - 1 = (2²²³ - 1) 2²²³ + (2²²² - 1)`.
-/

namespace VG.Proof.Ed448

open VG.Spec.X448
open VG.Proof.X448 (sqn pw pw_one pw_mul sqn_pw pow_pw)

/-- An addition chain for `z^((P - 3) / 4)`. -/
def rootPow (z : Fe) : Fe :=
  let t2 := sqn z 1 * z            -- 2^2 - 1
  let t4 := sqn t2 2 * t2          -- 2^4 - 1
  let t8 := sqn t4 4 * t4          -- 2^8 - 1
  let t16 := sqn t8 8 * t8         -- 2^16 - 1
  let t32 := sqn t16 16 * t16      -- 2^32 - 1
  let t64 := sqn t32 32 * t32      -- 2^64 - 1
  let t128 := sqn t64 64 * t64     -- 2^128 - 1
  let t192 := sqn t128 64 * t64    -- 2^192 - 1
  let t208 := sqn t192 16 * t16    -- 2^208 - 1
  let t216 := sqn t208 8 * t8      -- 2^216 - 1
  let t220 := sqn t216 4 * t4      -- 2^220 - 1
  let t222 := sqn t220 2 * t2      -- 2^222 - 1
  let t223 := sqn t222 1 * z       -- 2^223 - 1
  sqn t223 223 * t222

theorem rootPow_eq (z : Fe) : rootPow z = pow z ((P - 3) / 4) := by
  rw [pow_pw, ← congrArg rootPow (pw_one z)]
  simp only [rootPow, pw_mul, sqn_pw]
  exact congrArg (pw z) (by decide +kernel)

end VG.Proof.Ed448

import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Weierstrass.Complete
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# P-256 is a curve the proofs apply to

`p` is prime (`Prime.lean`), and `x³ - 3x + b` has no root modulo `p`, so the
curve has no point of order 2 (a certificate for `noTwoTorsion_of_cert`:
`g = x^p` and the inverse `v` of `g - x` modulo `x³ - 3x + b`, found by
computer algebra and checked by the kernel). The base point is on the curve.
-/

namespace VG.Proof.P256

open Spec.Weierstrass Weierstrass

instance fact_curve_p_prime : Fact (Nat.Prime Spec.P256.curve.p) := ⟨p_prime⟩

instance fact_curve_n_prime : Fact (Nat.Prime Spec.P256.curve.n) := ⟨n_prime⟩

/-- `-b` modulo `p`. -/
private def negB : Nat :=
  74733725485204106633371317169360305120971702399296588640698374994827630452660

/-- `x^p` modulo `x³ - 3x + b`. -/
private def xPow : Tri :=
  (66434390973925144466073271287821796038003695194169110494110089305650096453661,
    12402202686218762177567235911775779164004716598278868847786114277539554646092,
    24678849118215552148312087830792888746041224110560601850711771001608500700145)

/-- The inverse of `x^p - x` modulo `x³ - 3x + b`. -/
private def xPowInv : Tri :=
  (76626890310466861426869089647039036757962535851890885406097439786770458211455,
    74462945259064871768191128030512052509059297803194871526163573358218695456204,
    34768139465301476436978405170953382516735956999154666452188405812258086013549)

private theorem xPow_eq : powT Spec.P256.curve.p 3 negB 256 (0, 1, 0) Spec.P256.curve.p = xPow := by
  decide +kernel

private theorem xPowInv_mul : mulT Spec.P256.curve.p 3 negB xPowInv
    (xPow.1, (xPow.2.1 + Spec.P256.curve.p - 1) % Spec.P256.curve.p, xPow.2.2) = (1, 0, 0) := by
  decide +kernel

theorem noTwoTorsion : ∀ x : ZMod Spec.P256.curve.p,
    x ^ 3 + (Spec.P256.curve.a : ZMod Spec.P256.curve.p) * x +
      (Spec.P256.curve.b : ZMod Spec.P256.curve.p) ≠ 0 :=
  noTwoTorsion_of_cert Spec.P256.curve 3 negB 256 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) xPow xPowInv xPow_eq xPowInv_mul

theorem good : Good Spec.P256.curve where
  prime := p_prime
  gt3 := by decide +kernel
  noTwoTorsion := noTwoTorsion

theorem onCurve_G : onCurve Spec.P256.curve (G Spec.P256.curve) = true := by
  decide +kernel

end VG.Proof.P256

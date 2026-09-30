import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte

/-!
# ML-DSA: the coefficient of a half-byte, without a branch

Untrusted: everything here is checked by Lean. An implementation can compute
the coefficient `rbC η b` of an accepted half-byte (`HalfByte.lean`) modulo
`q` without a branch or a table (`hbVal`): `b mod 5` by subtracting 10 and
then 5 where they are no greater (`csubV`, a subtraction plus the subtrahend
masked by its borrow), and `(η - b') mod q` as `η - b'` plus `q` masked by
the borrow (`etaV`); `hbVal_eq` checks it on the accepted half-bytes by
evaluation.
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- `x - s` if `s ≤ x`: `x - s` plus `s` masked by the borrow. -/
def csubV (s x : BitVec 32) : BitVec 32 :=
  x - s + (0#32 - (BitVec.ofBool (decide (x.toNat < s.toNat))).setWidth 32 &&& s)

/-- `(η - x) mod q`: `η - x` plus `q` masked by the borrow. -/
def etaV (η x : BitVec 32) : BitVec 32 :=
  η - x + (0#32 - (BitVec.ofBool (decide (η.toNat < x.toNat))).setWidth 32 &&& 8380417#32)

/-- The coefficient of the half-byte `x`, modulo `q`, computed without a
branch: `η - (x mod 5)` for `η = 2`, `η - x` for `η = 4`. -/
def hbVal : Nat → BitVec 32 → BitVec 32
  | 2, x => etaV 2 (csubV 5 (csubV 10 x))
  | _, x => etaV 4 x

theorem hbVal_eq2 : ∀ b < 15, hbVal 2 (BitVec.ofNat 32 b) = zw (ofInt (rbC 2 b)) := by decide

theorem hbVal_eq4 : ∀ b < 9, hbVal 4 (BitVec.ofNat 32 b) = zw (ofInt (rbC 4 b)) := by decide

theorem hbVal_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < rbB η) :
    hbVal η (BitVec.ofNat 32 b) = zw (ofInt (rbC η b)) := by
  rcases hη with rfl | rfl
  · exact hbVal_eq2 b hb
  · exact hbVal_eq4 b hb

end VG.Proof.MlDsa.Sample

import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded

/-!
# ML-DSA: the coefficient of a half-byte, without a branch

Untrusted: everything here is checked by Lean. `CoeffFromHalfByte`
(Algorithm 15) accepts the half-bytes less than `hbBound η` and gives them
the coefficient `hbCoef η b` (`coeffFromHalfByte_eq'`, `hbTry_eq'`,
`halfByteOk_eq`). An implementation can compute that coefficient modulo `q`
without a branch or a table (`hbVal`): `b mod 5` by subtracting 10 and then
5 where they are no greater (`csubV`, a subtraction plus the subtrahend
masked by its borrow), and `(η - b') mod q` as `η - b'` plus `q` masked by
the borrow (`etaV`); `hbVal_eq` checks it on the accepted half-bytes by
evaluation.
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def hbBound (η : Nat) : Nat := if η = 2 then 15 else 9

/-- The coefficient of an accepted half-byte. -/
def hbCoef (η b : Nat) : Int := if η = 2 then 2 - (b % 5 : Nat) else 4 - b

theorem coeffFromHalfByte_eq' {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    coeffFromHalfByte η b = if b < hbBound η then some (hbCoef η b) else none := by
  rcases hη with rfl | rfl <;> simp [coeffFromHalfByte, hbBound, hbCoef]

theorem hbTry_eq' {η : Nat} (hη : η = 2 ∨ η = 4) (L : List Zq) (b : Nat) :
    hbTry η L b = if b < hbBound η then L ++ [ofInt (hbCoef η b)] else L := by
  unfold hbTry
  rw [coeffFromHalfByte_eq' hη]
  by_cases h : b < hbBound η <;> simp [h]

theorem halfByteOk_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    halfByteOk η b = if b < hbBound η then 1 else 0 := by
  unfold halfByteOk
  rw [coeffFromHalfByte_eq' hη]
  by_cases h : b < hbBound η <;> simp [h]

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

theorem hbVal_eq2 : ∀ b < 15, hbVal 2 (BitVec.ofNat 32 b) = zw (ofInt (hbCoef 2 b)) := by decide

theorem hbVal_eq4 : ∀ b < 9, hbVal 4 (BitVec.ofNat 32 b) = zw (ofInt (hbCoef 4 b)) := by decide

theorem hbVal_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < hbBound η) :
    hbVal η (BitVec.ofNat 32 b) = zw (ofInt (hbCoef η b)) := by
  rcases hη with rfl | rfl
  · exact hbVal_eq2 b hb
  · exact hbVal_eq4 b hb

end VG.Proof.MlDsa.Sample

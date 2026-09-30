import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded

/-!
# ML-DSA: `CoeffFromHalfByte` as a bound and a formula, for every target

Untrusted: everything here is checked by Lean. For `η = 2` or `4`,
`CoeffFromHalfByte` accepts the half-bytes less than `rbB η` and gives
`rbC η b` for them (`coeffFromHalfByte_eq`), so a try appends that
coefficient exactly when the half-byte is less than the bound (`hbTry_eq`),
and whether it does is `halfByteOk` (`halfByteOk_eq`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbB (η : Nat) : Nat := if η = 2 then 15 else 9

/-- The coefficient of an accepted half-byte. -/
def rbC (η b : Nat) : Int := if η = 2 then 2 - (b % 5 : Nat) else 4 - b

theorem coeffFromHalfByte_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    coeffFromHalfByte η b = if b < rbB η then some (rbC η b) else none := by
  rcases hη with rfl | rfl <;> simp [coeffFromHalfByte, rbB, rbC]

theorem hbTry_eq {η : Nat} (hη : η = 2 ∨ η = 4) (L : List Zq) (b : Nat) :
    hbTry η L b = if b < rbB η then L ++ [ofInt (rbC η b)] else L := by
  unfold hbTry
  rw [coeffFromHalfByte_eq hη]
  by_cases h : b < rbB η <;> simp [h]

theorem halfByteOk_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    halfByteOk η b = if b < rbB η then 1 else 0 := by
  unfold halfByteOk
  rw [coeffFromHalfByte_eq hη]
  by_cases h : b < rbB η <;> simp [h]

end VG.Proof.MlDsa.Sample

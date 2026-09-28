/-!
# Keccak-f[1600]: tables shared by the implementations

ρ's rotations and π's lane permutation, as tables, for every target's
implementation. (`Proof/Sha3/Spec.lean` proves them against the
specification.)
-/

namespace VG.Impl.Sha3

/-- The rotation (left) of lane `i` by ρ (Algorithm 2), as a table. -/
def rhoOff (i : Nat) : Nat :=
  [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8,
    18, 2, 61, 56, 14].getD i 0

/-- The lane of `A` that π moves to `(x, y)`: `((x + 3y) mod 5, x)`. -/
def piSrc (x y : Nat) : Nat := (x + 3 * y) % 5 + 5 * x

end VG.Impl.Sha3

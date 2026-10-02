import VerifiedGarbage.Impl.Ed25519.AArch64.PointMul

/-!
# Cached points

A cached point `[Y - X, Y + X, 2dT, 2Z]` is added with eight
multiplications (`pointAddCached`), and stored from constants
(`cachedPointStore`).
-/

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

/-- Add the cached point in slots 4–7 (`[Y - X, Y + X, 2dT, 2Z]` of `q`) to
the point in slots 0–3: the specification's `pointAdd p q`, in place.
Slots 8–15 are temporary. -/
def pointAddCachedOps : List FieldOp := [
  .sub 8 1 0, .mul 8 8 4,
  .add 9 1 0, .mul 9 9 5,
  .mul 10 3 6, .mul 11 2 7,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

def pointAddCached : List Instr := fieldCode pointAddCachedOps

/-- The table entry addressed by `x8` to slots 4–7. -/
def pointFromTableQ : List Instr :=
  (List.range 4).flatMap fun j => fromTableWords (32 * j) ++ stores (192 + 32 * j) .x4 .x5 .x6 .x7

/-- A field constant to workspace byte `dst`. -/
def cachedFieldStore (v : Spec.X25519.Fe) (dst : Nat) : List Instr := constWords v ++ store4 dst

/-- A cached point to the table entry at workspace byte `dst`. -/
def cachedPointStore (q : Spec.Ed25519.Point) (dst : Nat) : List Instr :=
  cachedFieldStore q.X dst ++ (cachedFieldStore q.Y (dst + 32) ++
    (cachedFieldStore q.Z (dst + 64) ++ cachedFieldStore q.T (dst + 96)))

end VG.Impl.Ed25519.AArch64

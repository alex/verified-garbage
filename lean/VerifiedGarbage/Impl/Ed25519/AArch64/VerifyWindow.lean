import VerifiedGarbage.Impl.Ed25519.BaseMultiples
import VerifiedGarbage.Impl.Ed25519.AArch64.BaseMultiply

/-!
# Verification's equation with 4-bit windows

Verification may leak its inputs, so its scalars `S` and `k` are public. It
computes `[k]A - [S]B` with one chain of doublings (`dblOps`), four per 4-bit window
of the scalars, from the top: each window adds `[a]A` for `k`'s digit `a`
from a table of `[1]A … [15]A` built at run time (byte 5376, cached), and `[-b]B`
for `S`'s digit `b` from constants (`negBaseCached`, byte 2048). A zero
digit adds nothing. The digits are read from the inputs, byte by byte (the
counter at byte 56), high nibble first: `k`'s 64 bytes, of which only the
low 32 have a byte of `S` beside them. The leading zero bytes of `k` above
its low 32 are skipped (`skipZero`): before them the sum is zero, which
doubles to itself. The equation `[S]B = R + [k]A` holds exactly when the
result equals `-R`, which the projective comparison `pointEqual` checks.
-/

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

/-- Slots 0–3 to the point at byte `o`, beyond the multiplication workspace. -/
def pointTableWrite (o : Nat) : List Instr :=
  [.movz .w .x19 0 0] ++ tableAddr o ++ pointToTable

/-- The point at byte `o` to slots 0–3. -/
def pointTableRead (o : Nat) : List Instr :=
  [.movz .w .x19 0 0] ++ tableAddr o ++ pointFromTable

/-- Doubles slots 0–3 in place with `dbl-2008-hwcd` (for `a = -1`): `A = X²`, `B = Y²`,
`C = 2Z²`, `E = 2XY`, `G = B - A`, `F = C - G`, `H = A + B`, and `X = EF`, `Y = GH`,
`Z = FG`, and `T = EH` if `t` (only an addition reads `T`). -/
def dblOps (t : Bool) : List FieldOp :=
  [.sqr 8 0, .sqr 9 1, .sqr 10 2, .add 10 10 10, .mul 11 0 1, .add 11 11 11,
    .sub 12 9 8, .sub 13 10 12, .add 14 8 9, .mul 0 11 13, .mul 1 12 14, .mul 2 13 12] ++
    if t then [.mul 3 11 14] else []

/-- Four doublings: three without `T`, with the counter `x1`, then one with it. -/
def doubleWindow : Prog isa :=
  .seq (.block [.movz .w .x1 3 0]) (.seq
    (.loop (.block (fieldCode (dblOps false) ++ [.subImm .x .x1 .x1 1])) (.nonzero .x .x1))
    (.block (fieldCode (dblOps true))))

/-- `[Y - X, Y + X, 2dT, 2Z]` of the point in slots 17–20 into slots 0–3, with `d` in slot 16. -/
def cacheOps : List FieldOp := [.sub 0 18 17, .add 1 18 17, .add 2 20 20, .mul 2 2 16, .add 3 19 19]

/-- The point in slots 0–3, cached, to entry `x19` of the table at byte 5376; slots 0–3 are kept. -/
def storeCached : List Instr :=
  fieldCode (savePointOps ++ cacheOps) ++ tableAddr 5376 ++ pointToTable ++ restorePoint

/-- `A` from byte 7424 into slots 0–3, cached into the table's entry 0 and into slots 4–7. -/
def aTableInit : List Instr :=
  pointTableRead 7424 ++ ([.movz .w .x19 0 0] : List Instr) ++ storeCached ++ tableAddr 5376 ++
    pointFromTableQ ++ [.movz .w .x19 1 0]

/-- Entry `x19` = entry `x19 - 1` (in slots 0–3) + `A` (cached in slots 4–7), cached; `x8` is
nonzero while another entry follows. -/
def aTableBody : List Instr :=
  pointAddCached ++ storeCached ++ [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 15]

/-- Entries `j < 15` of the table at byte 5376 are cached `[j + 1]A`. -/
def aTable : Prog isa := .seq (.block aTableInit) (.loop (.block aTableBody) (.nonzero .x .x8))

/-- Entries `j < 15` of the table at byte 2048 are cached `-[j + 1]B`. -/
def bTable : List Instr :=
  (List.range 15).flatMap fun i => cachedPointStore (negBaseCached i) (2048 + 128 * i)

/-- `x19` = byte `counter` of the scalar at the pointer stored at byte `ptr`, plus `add`. -/
def digitByte (ptr add : Nat) : List Instr :=
  [ld .x2 ptr, ld .x8 56, .add .x .x8 .x2 .x8, .ldrb .x19 .x8 add]

/-- The byte's high nibble. -/
def digitHigh (ptr add : Nat) : List Instr := digitByte ptr add ++ [.lsr .x .x19 .x19 4]

/-- The byte's low nibble. -/
def digitLow (ptr add : Nat) : List Instr :=
  digitByte ptr add ++ [.lsl .x .x19 .x19 60, .lsr .x .x19 .x19 60]

/-- Add entry `x19 - 1` of the table at byte `o`, unless `x19` is zero. -/
def addDigit (o : Nat) (add : List Instr) : Prog isa :=
  .ite (.nonzero .x .x19)
    (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
    (.block [])

/-- `pointAddCached` but for `T`, when a doubling follows, which does not read it. -/
def pointAddCachedP : List Instr := fieldCode pointAddCachedOps.dropLast

/-- Four doublings, then `k`'s digit, added with `add`. -/
def windowWith (digit add : List Instr) : Prog isa :=
  .seq doubleWindow (.seq (.block digit) (addDigit 5376 add))

/-- A window of `k` alone. -/
def windowA (digit : List Instr) : Prog isa := windowWith digit pointAddCachedP

/-- A window of `k` and of `S`: `S`'s addition reads the `T` of `k`'s. -/
def windowAB (digitA digitB : List Instr) : Prog isa :=
  .seq (windowWith digitA pointAddCached) (.seq (.block digitB) (addDigit 2048 pointAddCachedP))

/-- `x19` = the counter less 32: nonzero while a byte of `k` alone follows. -/
def aboveLow : List Instr := [ld .x19 56, .subImm .x .x19 .x19 32]

/-- A byte of `k` alone (bytes 63 down to 32). -/
def byteStepA : Prog isa :=
  .seq (.block batchBegin) (.seq (windowA (digitHigh 7952 0))
    (.seq (windowA (digitLow 7952 0)) (.block aboveLow)))

/-- A byte of `k` and of `S` (bytes 31 down to 0). -/
def byteStepAB : Prog isa :=
  .seq (.block batchBegin) (.seq (windowAB (digitHigh 7952 0) (digitHigh 7944 32))
    (.seq (windowAB (digitLow 7952 0) (digitLow 7944 32)) (.block batchTest)))

/-- `x19` = byte `c - 1` of `k`, for the counter `c`, which is `x8 + 1`. -/
def skipLoad : List Instr :=
  [ld .x8 56, .subImm .x .x8 .x8 1, ld .x2 7952, .add .x .x2 .x2 .x8, .ldrb .x19 .x2 0]

/-- Below a zero byte, the counter moves down; `x19` is nonzero while another
byte of `k` alone may be skipped. -/
def skipBody : Prog isa :=
  .seq (.block skipLoad) (.ite (.nonzero .x .x19) (.block [.movz .w .x19 0 0])
    (.block [st .x8 56, .subImm .x .x19 .x8 32]))

/-- Skip the leading zero bytes of `k` above its low 32. -/
def skipZero : Prog isa := .loop skipBody (.nonzero .x .x19)

/-- The bytes of `k` alone that are left after `skipZero`. -/
def windowsA : Prog isa :=
  .seq (.block aboveLow) (.ite (.nonzero .x .x19) (.loop byteStepA (.nonzero .x .x19)) (.block []))

/-- `-R` from byte 7552 into slots 4–7. -/
def negR : List Instr :=
  [.movz .w .x19 0 0] ++ tableAddr 7552 ++ pointFromTableQ ++ fieldCode [.const 8 0, .sub 4 8 4, .sub 7 8 7]

def windowSetup : List Instr := constField 16 Spec.Ed25519.d

def windowInit : List Instr := constPoint Spec.Ed25519.identity ++ mulCounterInit 64

end VG.Impl.Ed25519.AArch64

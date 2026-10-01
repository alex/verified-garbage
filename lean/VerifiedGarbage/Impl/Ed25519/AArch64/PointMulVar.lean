import VerifiedGarbage.Impl.Ed25519.AArch64.BaseMultiply
import VerifiedGarbage.Impl.Ed25519.AArch64.PointFromScalar

/-!
# Variable-time scalar multiplication, for verification

Verification may leak its inputs, so its scalars are public. The bit loop
branches on each bit: a set bit adds its power, and a clear bit does
nothing, with no masked selection. `add` is the addition: `pointAdd` for
the exact powers of a point, `pointAddCached` for the cached powers of the
base point.
-/

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

/-- `x3` = bit `x1 + x19` of the scalar. -/
def scalarBitLoad : List Instr := [.add .x .x8 .x19 .x1, .add .x .x8 .x0 .x8, .ldrb .x3 .x8 768]

/-- Add local table entry `x19` to the accumulator. -/
def addEntry (add : List Instr) : List Instr := tableAddr 5376 ++ pointFromTableQ ++ add

def accumulateVarBody (add : List Instr) : Prog isa :=
  .seq (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ scalarBitLoad))
    (.ite (.nonzero .x .x3) (.block (addEntry add)) (.block []))

def accumulateVar16 (add : List Instr) : Prog isa :=
  .seq (.block [.movz .w .x19 16 0]) (.loop (accumulateVarBody add) (.nonzero .x .x19))

/-- `pointMulBatch`, adding only for set bits. -/
def pointMulBatchVar : Prog isa :=
  .seq (.block batchBegin) (.seq prepareBatch (.seq (.block batchBitOffset)
    (.seq (accumulateVar16 pointAdd) (.block batchTest))))

def pointMultiplyVar (count : Nat) : Prog isa :=
  .seq (pointMultiplyInit count) (.loop pointMulBatchVar (.nonzero .x .x19))

def pointFromScalarVar (count : Nat) : Prog isa :=
  .seq (pointFromScalarPrepare count) (pointMultiplyVar count)

/-- A batch of the base point's cached powers, adding only for set bits. -/
def baseMulBatchVar : Prog isa :=
  .seq (.block batchBegin) (.seq baseBatchTable (.seq (.block batchBitOffset)
    (.seq (accumulateVar16 pointAddCached) (.block batchTest))))

def baseMultiplyVar : Prog isa := .seq (.block baseMultiplyInit) (.loop baseMulBatchVar (.nonzero .x .x19))

/-- `[s]B` for the 32-byte scalar at `x1`. -/
def baseFromScalarVar : Prog isa := .seq (pointFromScalarPrepare 16) baseMultiplyVar

end VG.Impl.Ed25519.AArch64

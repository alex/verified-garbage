import VerifiedGarbage.Impl.Ed25519.X86_64.BaseMultiply
import VerifiedGarbage.Impl.Ed25519.X86_64.PointFromScalar

/-!
# Variable-time scalar multiplication, for verification

Verification may leak its inputs, so its scalars are public. The bit loop
branches on each bit: a set bit adds its power, and a clear bit does
nothing, with no masked selection. `add` is the addition: `pointAdd` for
the exact powers of a point, `pointAddCached` for the cached powers of the
base point.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (stores)

/-- ZF clear exactly when bit `rsi + rbx` of the scalar is set. -/
def scalarBitTest : List Instr :=
  [.mov .rax (.reg .rbx), .alu .add .rax (.reg .rsi),
    .movzx8 .rcx { base := .rdi, index := some .rax, disp := 768 }, .alu .test .rcx (.reg .rcx)]

/-- A table entry addressed by `rax` to slots 4–7. -/
def pointFromTableQ : List Instr :=
  (List.range 4).flatMap fun j => fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11

/-- Add local table entry `rbx` to the accumulator. -/
def addEntry (add : List Instr) : List Instr := tableAddr 5376 ++ pointFromTableQ ++ add

def accumulateVarBody (add : List Instr) : Prog isa :=
  .seq (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ scalarBitTest))
    (.seq (.ite .ne (.block (addEntry add)) (.block []))
      (.block [.alu .test .rbx (.reg .rbx)]))

def accumulateVar16 (add : List Instr) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 16)]) (.loop (accumulateVarBody add) .ne)

/-- `pointMulBatch`, adding only for set bits. -/
def pointMulBatchVar : Prog isa :=
  .seq (.block batchBegin) (.seq prepareBatch (.seq (.block batchBitOffset)
    (.seq (accumulateVar16 pointAdd) (.block batchTest))))

def pointMultiplyVar (count : Nat) : Prog isa :=
  .seq (pointMultiplyInit count) (.loop pointMulBatchVar .ne)

def pointFromScalarVar (count : Nat) : Prog isa :=
  .seq (pointFromScalarPrepare count) (pointMultiplyVar count)

/-- `baseMulBatch`, adding only for set bits. -/
def baseMulBatchVar : Prog isa :=
  .seq (.block batchBegin) (.seq baseBatchTable (.seq (.block batchBitOffset)
    (.seq (accumulateVar16 pointAddCached) (.block batchTest))))

def baseMultiplyVar : Prog isa := .seq (.block baseMultiplyInit) (.loop baseMulBatchVar .ne)

/-- `[s]B` for the 32-byte scalar at `rsi`. -/
def baseFromScalarVar : Prog isa := .seq (pointFromScalarPrepare 16) baseMultiplyVar

end VG.Impl.Ed25519.X86_64

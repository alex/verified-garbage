import VerifiedGarbage.Impl.Ed25519.BaseTable
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul

/-!
# Base-point multiplication from a precomputed table

The scalar's 256 bits are consumed in sixteen batches of sixteen, from the
top, as in `pointMultiply`. Instead of doubling a checkpoint sixteen times,
each batch writes its sixteen powers of the base point into the local table
at byte 5376 from constants (`baseCached`), chosen by comparing the public
batch counter `rbx` with each batch index. The powers are cached as
`[Y - X, Y + X, 2dT, 2Z]`, so each addition takes eight multiplications.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

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

/-- One descending scalar bit, as `pointAccumulate`, adding a cached power. -/
def baseAccumulate : List Instr := prepareAdd ++ pointAddCached ++ scalarBitMask ++ pointSelect

def baseAccumulateBody : List Instr :=
  ([.alu .sub .rbx (.imm 1)] : List Instr) ++ baseAccumulate ++ [.alu .test .rbx (.reg .rbx)]

def baseAccumulate16 : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 16)]) (.loop (.block baseAccumulateBody) .ne)

/-- `rax` = the local table, at byte 5376 of the scratch. -/
def baseTableStart : List Instr := [.movImm64 .rax 5376, .alu .add .rax (.reg .rdi)]

/-- A field constant to byte `dst` from `rax`. -/
def cachedFieldStore (v : Spec.X25519.Fe) (dst : Nat) : List Instr := constWords v ++ tableWords dst

/-- A cached point to the table entry at byte `dst` from `rax`. -/
def cachedPointStore (q : Spec.Ed25519.Point) (dst : Nat) : List Instr :=
  cachedFieldStore q.X dst ++ (cachedFieldStore q.Y (dst + 32) ++
    (cachedFieldStore q.Z (dst + 64) ++ cachedFieldStore q.T (dst + 96)))

/-- The sixteen cached powers `[2^(16j + i)]B` of batch `j` to the local table. -/
def baseBatchStores (j : Nat) : List Instr :=
  baseTableStart ++ (List.range 16).flatMap fun i => cachedPointStore (baseCached (16 * j + i)) (128 * i)

/-- The stores of batch `rbx`, for the batch indices listed. -/
def baseBatchTableFrom : List Nat → Prog isa
  | [] => .block []
  | k :: ks => .seq (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 k))])
      (.ite .e (.block (baseBatchStores k)) (baseBatchTableFrom ks))

def baseBatchTable : Prog isa := baseBatchTableFrom (List.range 16)

/-- One batch: the counter, the batch's powers, then its sixteen bits. -/
def baseMulBatch : Prog isa :=
  .seq (.block batchBegin) (.seq baseBatchTable (.seq (.block batchBitOffset)
    (.seq baseAccumulate16 (.block batchTest))))

def baseMultiplyInit : List Instr := constPoint Spec.Ed25519.identity ++ mulCounterInit 16

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768 onward. -/
def baseMultiply : Prog isa := .seq (.block baseMultiplyInit) (.loop baseMulBatch .ne)

end VG.Impl.Ed25519.X86_64

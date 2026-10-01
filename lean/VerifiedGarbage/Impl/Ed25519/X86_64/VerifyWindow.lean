import VerifiedGarbage.Impl.Ed25519.X86_64.BaseMultiples
import VerifiedGarbage.Impl.Ed25519.X86_64.Cached

/-!
# Verification's equation with 4-bit windows

Verification may leak its inputs, so its scalars `S` and `k` are public. It
computes `[k]A - [S]B` with one chain of doublings (`dblOps`), four per 4-bit window
of the scalars, from the top: each window adds `[a]A` for `k`'s digit `a`
from a table of `[1]A … [15]A` built at run time (byte 5376), and `[-b]B`
for `S`'s digit `b` from constants (`negBaseCached`, byte 2048). A zero
digit adds nothing. The digits are read from the inputs, byte by byte (the
scratch counter at byte 56), high nibble first: `k`'s 64 bytes, of which
only the low 32 have a byte of `S` beside them. The equation
`[S]B = R + [k]A` holds exactly when the result equals `-R`, which the
projective comparison `pointEqual` checks.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (sc stores)

/-- A table entry addressed by `rax` to slots 4–7. -/
def pointFromTableQ : List Instr :=
  (List.range 4).flatMap fun j => fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11

/-- `rax` = byte `o` of the scratch. -/
def tableStart (o : Nat) : List Instr := [.movImm64 .rax (BitVec.ofNat 64 o), .alu .add .rax (.reg .rdi)]

/-- Doubles slots 0–3 in place with `dbl-2008-hwcd` (for `a = -1`): `A = X²`, `B = Y²`,
`C = 2Z²`, `E = 2XY`, `G = B - A`, `F = C - G`, `H = A + B`, and `X = EF`, `Y = GH`,
`Z = FG`, and `T = EH` if `t` (only an addition reads `T`). -/
def dblOps (t : Bool) : List FieldOp :=
  [.sqr 8 0, .sqr 9 1, .sqr 10 2, .add 10 10 10, .mul 11 0 1, .add 11 11 11,
    .sub 12 9 8, .sub 13 10 12, .add 14 8 9, .mul 0 11 13, .mul 1 12 14, .mul 2 13 12] ++
    if t then [.mul 3 11 14] else []

/-- Four doublings: three without `T`, with the counter `rsi`, then one with it. -/
def double4 (fld : Arith) : Prog isa :=
  .seq (.block [.mov32 .rsi (.imm 3)]) (.seq
    (.loop (.block (fieldCode fld (dblOps false) ++ [.alu .sub .rsi (.imm 1)])) .ne)
    (.block (fieldCode fld (dblOps true))))

/-- `[1]A` from byte 7424 into slots 0–3 and into the table's entry 0. -/
def aTableInit : List Instr :=
  tableStart 7424 ++ pointFromTable ++ ([.mov32 .rbx (.imm 0)] : List Instr) ++ tableAddr 5376 ++
    pointToTable ++ [.mov32 .rbx (.imm 1)]

/-- Entry `rbx` = entry `rbx - 1` (in slots 0–3) + A. -/
def aTableBody (fld : Arith) : List Instr :=
  tableStart 7424 ++ pointFromTableQ ++ pointAdd fld ++ tableAddr 5376 ++ pointToTable ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 15)]

/-- Entries `j < 15` of the table at byte 5376 are `[j + 1]A`. -/
def aTable (fld : Arith) : Prog isa := .seq (.block aTableInit) (.loop (.block (aTableBody fld)) .ne)

/-- Entries `j < 15` of the table at byte 2048 are cached `-[j + 1]B`. -/
def bTable : List Instr :=
  tableStart 2048 ++ (List.range 15).flatMap fun i => cachedPointStore (negBaseCached i) (128 * i)

/-- `rbx` = byte `counter` of the scalar at the pointer stored at byte `ptr` of the scratch,
plus `add`. -/
def digitByte (ptr add : Nat) : List Instr :=
  [.mov .rsi (.mem (sc ptr)), .alu .add .rsi (.imm (BitVec.ofNat 32 add)), .mov .rax (.mem (sc 56)),
    .movzx8 .rbx { base := .rsi, index := some .rax }]

/-- The byte's high nibble, ZF set if it is zero. -/
def digitHigh (ptr add : Nat) : List Instr :=
  digitByte ptr add ++ [.shift .shr .rbx 4, .alu .test .rbx (.reg .rbx)]

/-- The byte's low nibble, ZF set if it is zero. -/
def digitLow (ptr add : Nat) : List Instr := digitByte ptr add ++ [.alu .and .rbx (.imm 15)]

/-- Add entry `rbx - 1` of the table at byte `o`, unless `rbx` is zero. -/
def addDigit (o : Nat) (add : List Instr) : Prog isa :=
  .ite .ne (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
    (.block [])

/-- A window of `k` alone. -/
def windowA (fld : Arith) (digit : List Instr) : Prog isa :=
  .seq (double4 fld) (.seq (.block digit) (addDigit 5376 (pointAdd fld)))

/-- A window of `k` and of `S`. -/
def windowAB (fld : Arith) (digitA digitB : List Instr) : Prog isa :=
  .seq (windowA fld digitA) (.seq (.block digitB) (addDigit 2048 (pointAddCached fld)))

/-- A byte of `k` alone (bytes 63 down to 32). -/
def byteStepA (fld : Arith) : Prog isa :=
  .seq (.block batchBegin) (.seq (windowA fld (digitHigh 7952 0))
    (.seq (windowA fld (digitLow 7952 0)) (.block [.mov .rbx (.mem (sc 56)), .alu .cmp .rbx (.imm 32)])))

/-- A byte of `k` and of `S` (bytes 31 down to 0). -/
def byteStepAB (fld : Arith) : Prog isa :=
  .seq (.block batchBegin) (.seq (windowAB fld (digitHigh 7952 0) (digitHigh 7944 32))
    (.seq (windowAB fld (digitLow 7952 0) (digitLow 7944 32)) (.block batchTest)))

/-- `-R` from byte 7552 into slots 4–7. -/
def negR (fld : Arith) : List Instr :=
  tableStart 7552 ++ pointFromTableQ ++ fieldCode fld [.const 8 0, .sub 4 8 4, .sub 7 8 7]

def windowSetup : List Instr := constField 16 Spec.Ed25519.d

def windowInit (fld : Arith) : List Instr := constPoint fld Spec.Ed25519.identity ++ mulCounterInit 64

end VG.Impl.Ed25519.X86_64

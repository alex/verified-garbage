import VerifiedGarbage.Impl.Ed25519.X86_64.PointBatch

/-! Descend through checkpoint batches with a public counter in scratch. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (sc)

/-- Decrement the remaining batch count, retaining it across table generation. -/
def batchBegin : List Instr :=
  [.mov .rbx (.mem (sc 56)), .alu .sub .rbx (.imm 1), .store (sc 56) .rbx]

def batchBitOffset : List Instr :=
  [.mov .rax (.mem (sc 56)), .movImm64 .rcx 16, .mul .rcx, .mov .rsi (.reg .rax)]

def batchTest : List Instr := [.mov .rbx (.mem (sc 56)), .alu .test .rbx (.reg .rbx)]

def pointMulBatch (fld : Arith) : Prog isa :=
  .seq (.block batchBegin) (.seq (prepareBatch fld) (.seq (.block batchBitOffset)
    (.seq (accumulate16 fld) (.block batchTest))))

def mulCounterInit (count : Nat) : List Instr :=
  [.movImm64 .rax (BitVec.ofNat 64 count), .store (sc 56) .rax]

/-- The input point is in slots 0-3; scalar bits were expanded into bytes 768 onward. -/
def pointMultiplyInit (fld : Arith) (count : Nat) : Prog isa :=
  .seq (pointPowers fld 1280 count true) (.seq (.block (constPoint fld Spec.Ed25519.identity))
    (.block (mulCounterInit count)))

def pointMultiply (fld : Arith) (count : Nat) : Prog isa :=
  .seq (pointMultiplyInit fld count) (.loop (pointMulBatch fld) .ne)

end VG.Impl.Ed25519.X86_64

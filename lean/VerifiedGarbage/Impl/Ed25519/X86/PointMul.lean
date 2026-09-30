import VerifiedGarbage.Impl.Ed25519.X86.PointBatch

/-! Descending batches, with the public remaining count at workspace byte28. -/
namespace VG.Impl.Ed25519.X86
open VG.X86
open VG.Impl.X25519.X86 (sc)

def batchBegin : List Instr :=
  [.mov .esi (.mem (sc 28)), .alu .sub .esi (.imm 1), .store (sc 28) .esi]
def batchTest : List Instr := [.mov .esi (.mem (sc 28)), .alu .test .esi (.reg .esi)]
def pointMulBatch : Prog isa :=
  .seq (.block batchBegin) (.seq prepareBatch (.seq accumulate16 (.block batchTest)))
def mulCounterInit (count : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 count)), .store (sc 28) .eax]
def pointMultiplyInit (count : Nat) : Prog isa :=
  .seq (pointPowers 1024 count true)
    (.seq (.block (constPoint Spec.Ed25519.identity)) (.block (mulCounterInit count)))
def pointMultiply (count : Nat) : Prog isa :=
  .seq (pointMultiplyInit count) (.loop pointMulBatch .ne)

end VG.Impl.Ed25519.X86

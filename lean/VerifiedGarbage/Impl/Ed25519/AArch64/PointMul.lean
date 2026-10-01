import VerifiedGarbage.Impl.Ed25519.AArch64.PointBatch

/-! Descend through checkpoint batches with the counter at workspace byte 56. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def batchBegin : List Instr := [ld .x19 56, .subImm .x .x19 .x19 1, st .x19 56]
def batchBitOffset : List Instr := [ld .x8 56, .lsl .x .x1 .x8 4]
def batchTest : List Instr := [ld .x19 56]

def mulCounterInit (count : Nat) : List Instr := const64 .x8 (BitVec.ofNat 64 count) ++ [st .x8 56]

def pointMultiplyInit (count : Nat) : Prog isa :=
  .seq (pointPowers 1280 count true) (.seq (.block (constPoint Spec.Ed25519.identity))
    (.block (mulCounterInit count)))

end VG.Impl.Ed25519.AArch64

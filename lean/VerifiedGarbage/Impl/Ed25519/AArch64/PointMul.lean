import VerifiedGarbage.Impl.Ed25519.AArch64.PointTable

/-! A descending byte counter at workspace byte 56. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def batchBegin : List Instr := [ld .x19 56, .subImm .x .x19 .x19 1, st .x19 56]
def batchTest : List Instr := [ld .x19 56]

def mulCounterInit (count : Nat) : List Instr := const64 .x8 (BitVec.ofNat 64 count) ++ [st .x8 56]

end VG.Impl.Ed25519.AArch64

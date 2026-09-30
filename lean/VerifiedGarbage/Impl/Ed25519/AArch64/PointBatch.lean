import VerifiedGarbage.Impl.Ed25519.AArch64.PointPowers
import VerifiedGarbage.Impl.Ed25519.AArch64.PointAccumulateLoop

/-! Rebuild adjacent powers from a checkpoint without losing the accumulator. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def loadCheckpoint : List Instr := savePoint ++ tableAddr 1280 ++ pointFromTable

def prepareBatch : Prog isa :=
  .seq (.block loadCheckpoint) (.seq (pointPowers 5376 16 false) (.block restorePoint))

end VG.Impl.Ed25519.AArch64

import VerifiedGarbage.Impl.Ed25519.X86_64.PointPowers
import VerifiedGarbage.Impl.Ed25519.X86_64.PointAccumulateLoop

/-! Rebuild sixteen adjacent powers from a checkpoint, preserving the accumulator. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

def loadCheckpoint : List Instr := savePoint ++ tableAddr 1280 ++ pointFromTable

def prepareBatch : Prog isa :=
  .seq (.block loadCheckpoint) (.seq (pointPowers 5376 16 false) (.block restorePoint))

end VG.Impl.Ed25519.X86_64

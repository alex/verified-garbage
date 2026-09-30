import VerifiedGarbage.Impl.Ed25519.X86.PointPowers
import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate

/-! Rebuild a local batch while preserving the scalar accumulator. -/
namespace VG.Impl.Ed25519.X86
open VG.X86

def loadCheckpoint : List Instr := savePoint ++ tableAddr 1024 ++ pointFromTable
def prepareBatch : Prog isa :=
  .seq (.block loadCheckpoint) (.seq (pointPowers 5120 16 false) (.block restorePoint))

end VG.Impl.Ed25519.X86

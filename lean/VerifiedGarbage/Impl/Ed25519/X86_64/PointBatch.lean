import VerifiedGarbage.Impl.Ed25519.X86_64.PointPowers
import VerifiedGarbage.Impl.Ed25519.X86_64.PointAccumulateLoop

/-! Rebuild sixteen adjacent powers from a checkpoint, preserving the accumulator. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

def loadCheckpoint (fld : Arith) : List Instr := savePoint fld ++ tableAddr 1280 ++ pointFromTable

def prepareBatch (fld : Arith) : Prog isa :=
  .seq (.block (loadCheckpoint fld)) (.seq (pointPowers fld 5376 16 false) (.block (restorePoint fld)))

end VG.Impl.Ed25519.X86_64

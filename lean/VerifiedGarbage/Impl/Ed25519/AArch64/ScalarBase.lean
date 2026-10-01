import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
import VerifiedGarbage.Impl.Ed25519.AArch64.Bits
import VerifiedGarbage.Impl.Ed25519.AArch64.BaseMultiply
import VerifiedGarbage.Impl.Ed25519.AArch64.PointEncode

/-! Base-point multiplication for the full unsigned 256-bit input scalar, from the
precomputed, cached powers of the base point. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def scalarBasePrepare : Prog isa := scalarBits 32
def scalarBaseEngine : Prog isa := .seq scalarBasePrepare (.seq baseMultiply pointEncode)
def scalarBaseSetup : List Instr := [.str .x .x0 .x2 48, mov .x0 .x2]
def scalarBaseFinishArgs : List Instr := [mov .x2 .x0, ld .x0 48]
def scalarBaseFinish : Prog isa := .seq (.block scalarBaseFinishArgs) (.block scalarFinish)

def scalarBase : Prog isa :=
  .seq (.block (scalarSave ++ scalarBaseSetup)) (.seq scalarBaseEngine scalarBaseFinish)

end VG.Impl.Ed25519.AArch64

import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
import VerifiedGarbage.Impl.Ed25519.AArch64.Bits
import VerifiedGarbage.Impl.Ed25519.AArch64.PointMul
import VerifiedGarbage.Impl.Ed25519.AArch64.PointEncode

/-! Base-point multiplication for the full unsigned 256-bit input scalar. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def scalarBaseInit : List Instr := constField 16 Spec.Ed25519.d ++ constPoint Spec.Ed25519.basePoint
def scalarBasePrepare : Prog isa := .seq (scalarBits 32) (.block scalarBaseInit)
def scalarBaseEngine : Prog isa := .seq scalarBasePrepare (.seq (pointMultiply 16) pointEncode)
def scalarBaseSetup : List Instr := [.str .x .x0 .x2 48, mov .x0 .x2]
def scalarBaseFinishArgs : List Instr := [mov .x2 .x0, ld .x0 48]
def scalarBaseFinish : Prog isa := .seq (.block scalarBaseFinishArgs) (.block scalarFinish)

def scalarBase : Prog isa :=
  .seq (.block (scalarSave ++ scalarBaseSetup)) (.seq scalarBaseEngine scalarBaseFinish)

end VG.Impl.Ed25519.AArch64

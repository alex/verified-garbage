import VerifiedGarbage.Impl.Ed25519.X86.InputBits
import VerifiedGarbage.Impl.Ed25519.X86.PointMul
import VerifiedGarbage.Impl.Ed25519.X86.PointEncode

namespace VG.Impl.Ed25519.X86
open VG VG.X86

def baseSetupOps : List FieldOp := constPointOps Spec.Ed25519.basePoint ++ [.const 16 Spec.Ed25519.d]

def scalarBase : Code Instr Cond :=
  .seq (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps))
    (.seq (pointMultiply 16) (.seq pointEncode (.block (finishWords 96))))

end VG.Impl.Ed25519.X86

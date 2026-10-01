import VerifiedGarbage.Impl.Ed25519.Arm.RecoverSign

/-! Compare projective coordinates using the specification's cross products. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def pointEqualOps : List FieldOp := [.mul 8 0 6, .mul 9 4 2, .mul 10 1 6, .mul 11 5 2]
def pointEqual : Prog isa :=
  .seq (fieldCode pointEqualOps) (.seq (fieldEqual 8 9) (.ite .eq
    (.seq (fieldEqual 10 11) (.ite .eq (.block [.mov .r9 (.imm 1)]) recoverInvalid)) recoverInvalid))

end VG.Impl.Ed25519.Arm

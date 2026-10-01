import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
import VerifiedGarbage.Impl.Ed25519.Arm.PointEqual
import VerifiedGarbage.Impl.Ed25519.Arm.PointTableIO
import VerifiedGarbage.Impl.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarABI

/-! Strict Ed25519 verification with the entire 512-bit challenge. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def loadHeader (d : Nat) : List Instr := scratchAddr d ++ [.ldr .r12 .r12 0]
def verifyScalar : List Instr :=
  loadHeader 8132 ++ [.dp .add .r12 .r12 (.imm 32)] ++
    unpackField SR 0 ++ scalarCompare ++ [.cmp .r5 (.imm 0)]

def verifyLhs : Prog isa :=
  .seq (.block (loadHeader 8132 ++ [.dp .add .r12 .r12 (.imm 32)]))
    (.seq (constPoint Spec.Ed25519.basePoint)
      (.seq (pointFromScalar 16) (.block (pointTableWrite 8000))))

def verifyCombine : Prog isa :=
  .seq copyPointToQ (.seq (.block (pointTableRead 7872))
    (.seq pointAdd (.seq copyPointToQ (.block (pointTableRead 8000)))))

def verifyRhs : Prog isa :=
  .seq (.block (pointTableRead 7744 ++ loadHeader 8136))
    (.seq (pointFromScalar 32) (.seq verifyCombine pointEqual))

def verifyEquationPoints : Prog isa := .seq verifyLhs verifyRhs
def decodedThen (next : Prog isa) : Prog isa :=
  .seq (.block [.cmp .r9 (.imm 0)]) (.ite .ne next recoverInvalid)

def verifyDecodeR : Prog isa :=
  .seq (.block (loadHeader 8132)) (.seq pointDecode
    (decodedThen (.seq (.block (pointTableWrite 7872)) verifyEquationPoints)))

def verifyDecodeA : Prog isa :=
  .seq (.block (loadHeader 8128)) (.seq pointDecode
    (decodedThen (.seq (.block (pointTableWrite 7744)) verifyDecodeR)))

def verifyBody : Prog isa :=
  .seq (.block verifyScalar) (.ite .eq (.seq (.block initFields) verifyDecodeA) recoverInvalid)

def verifyHeaders : List Instr :=
  [.movw .r12 8128, .dp .add .r12 .r3 (.reg .r12),
    .str .r0 .r12 0, .str .r1 .r12 4, .str .r2 .r12 8, .mov .r0 (.reg .r3)]
def verifySetup : List Instr := scalarSave .r3 ++ verifyHeaders
def verifyFinish : List Instr :=
  [.mov .r1 (.reg .r9)] ++ scalarRestore ++ [.mov .r0 (.reg .r1)]
def verifyEquation : Prog isa :=
  .seq (.block verifySetup) (.seq verifyBody (.block verifyFinish))

end VG.Impl.Ed25519.Arm

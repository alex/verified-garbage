import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode
import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
import VerifiedGarbage.Impl.Ed25519.AArch64.PointMulVar

/-! Canonical point/scalar checks and the uncofactored verification equation
with the caller's full 512-bit SHA-512 challenge. A challenge below `2^256`
(a reduced one) takes half the doublings. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def pointTableWrite (o : Nat) : List Instr :=
  [.movz .w .x19 0 0] ++ tableAddr o ++ pointToTable

def pointTableRead (o : Nat) : List Instr :=
  [.movz .w .x19 0 0] ++ tableAddr o ++ pointFromTable

def loadScalarWords : List Instr :=
  [.ldr .x .x4 .x2 0, .ldr .x .x5 .x2 8, .ldr .x .x6 .x2 16, .ldr .x .x7 .x2 24]

/-- x8 is all ones precisely when the signature scalar is below L. -/
def verifyScalar : List Instr :=
  [ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0] ++
    loadScalarWords ++ scalarSubtract ++ [.sbcs .x .x8 .x10 .x10]

def pointEqualOps : List FieldOp := [.mul 8 0 6, .mul 9 4 2, .mul 10 1 6, .mul 11 5 2]

def pointEqual : Prog isa :=
  .seq (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (.ite (.zero .x .x8)
    (.seq (.block (fieldEqual 10 11))
      (.ite (.zero .x .x8) (.block [.movz .w .x8 1 0]) recoverInvalid)) recoverInvalid)

def verifyLhs : Prog isa :=
  .seq (.block [ld .x1 7944, .addImm .x .x1 .x1 32])
    (.seq baseFromScalarVar (.block (pointTableWrite 7680)))

def verifyCombine : List Instr :=
  copyPointToQ ++ pointTableRead 7552 ++ pointAdd ++ copyPointToQ ++ pointTableRead 7680

/-- `x8` is zero exactly when the challenge at `x1` is below `2^256`: its
upper 32 bytes are zero, as after `vg_ed25519_scalar_reduce`. -/
def challengeHigh : List Instr :=
  ([.addImm .x .x2 .x1 32] : List Instr) ++ loadScalarWords ++
    [.logic .orr .x .x8 .x4 .x5, .logic .orr .x .x9 .x6 .x7, .logic .orr .x .x8 .x8 .x9]

/-- `[k]A` for the challenge `k` at `x1`, with sixteen batches of bits when
`k < 2^256` (the challenge is public), or thirty-two. -/
def challengeMul : Prog isa :=
  .seq (.block challengeHigh) (.ite (.zero .x .x8) (pointFromScalarVar 16) (pointFromScalarVar 32))

def verifyRhsPrepare : Prog isa :=
  .seq (.block [ld .x1 7952]) (.seq (.block (pointTableRead 7424))
    (.seq challengeMul (.block verifyCombine)))

def verifyRhs : Prog isa := .seq verifyRhsPrepare pointEqual
def verifyEquationPoints : Prog isa := .seq verifyLhs verifyRhs
def decodedThen (next : Prog isa) : Prog isa := .ite (.nonzero .x .x8) next recoverInvalid

def verifyDecodeR : Prog isa :=
  .seq (.block [ld .x2 7944]) (.seq pointDecode
    (decodedThen (.seq (.block (pointTableWrite 7552)) verifyEquationPoints)))

def verifyDecodeA : Prog isa :=
  .seq (.block [ld .x2 7936]) (.seq pointDecode
    (decodedThen (.seq (.block (pointTableWrite 7424)) verifyDecodeR)))

def verifyHeaders : List Instr :=
  [.str .x .x0 .x2 7936, .str .x .x1 .x2 7944, .str .x .x8 .x2 7952, mov .x0 .x2]

def verifySetup : List Instr := ([mov .x8 .x2, mov .x2 .x3] : List Instr) ++ scalarSave ++ verifyHeaders

/-- `(pk, sig, challenge, scratch) = (x0, x1, x2, x3)`; boolean result in x0. -/
def verifyEquation : Prog isa :=
  .seq (.block verifySetup) (.seq
    (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid))
    (.block (([mov .x2 .x0, mov .x0 .x8] : List Instr) ++ scalarRestore)))

end VG.Impl.Ed25519.AArch64

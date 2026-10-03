import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode
import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyWindow

/-! Canonical point/scalar checks and the uncofactored verification equation
with the caller's full 512-bit SHA-512 challenge. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

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

/-- Returns 1 in x8 if `[S]B = R + [k]A`, for `A` at byte 7424 and `R` at byte 7552. -/
def verifyEquationPoints : Prog isa :=
  .seq (.block windowSetup) (.seq aTable (.seq (.block bTable) (.seq (.block windowInit)
    (.seq skipZero (.seq windowsA (.seq (.loop byteStepAB (.nonzero .x .x19))
      (.seq (.block negR) pointEqual)))))))

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

import VerifiedGarbage.Impl.Ed25519.X86.InputSlice
import VerifiedGarbage.Impl.Ed25519.X86.PointDecode
import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
import VerifiedGarbage.Impl.Ed25519.X86.Scalar

/-! Canonical decoding and the uncofactored verification equation using all
512 supplied challenge bits. The four cdecl arguments are pk, sig, challenge,
and scratch; the result is exactly zero or one in EAX. -/
namespace VG.Impl.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

def pointTableWrite (o : Nat) : List Instr :=
  [.mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 o))] ++ pointToTable

def pointTableRead (o : Nat) : List Instr :=
  [.mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 o))] ++ pointFromTable

def verifyScalar : List Instr := inputSliceWords 1 32 64 8 ++ scalarSubtract ++ [.alu .test .ebx (.reg .ebx)]

def pointEqualOps : List FieldOp := [.mul 8 0 6, .mul 9 4 2, .mul 10 1 6, .mul 11 5 2]
def pointEqual : Prog isa :=
  .seq (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (.ite .e
    (.seq (.block (fieldEqual 10 11)) (.ite .e (.block [.mov .eax (.imm 1)]) recoverInvalid)) recoverInvalid)

def pointFromInput (i skip bytes count : Nat) : Prog isa :=
  .seq (.block (inputSliceBits i skip bytes ++ fieldCode [.const 16 Spec.Ed25519.d])) (pointMultiply count)

def verifyLhs : Prog isa :=
  .seq (.block (constPoint Spec.Ed25519.basePoint))
    (.seq (pointFromInput 1 32 32 16) (.block (pointTableWrite 7936)))

def verifyCombine : List Instr :=
  copyPointToQ ++ pointTableRead 7808 ++ pointAdd ++ copyPointToQ ++ pointTableRead 7936

def verifyRhs : Prog isa :=
  .seq (.block (pointTableRead 7680))
    (.seq (pointFromInput 2 0 64 32) (.seq (.block verifyCombine) pointEqual))

def verifyEquationPoints : Prog isa := .seq verifyLhs verifyRhs

def decodedThen (next : Prog isa) : Prog isa :=
  .seq (.block [.alu .test .eax (.reg .eax)]) (.ite .ne next recoverInvalid)

def verifyDecodeR : Prog isa :=
  .seq (.block (inputSliceWords 1 0 96 8)) (.seq pointDecode
    (decodedThen (.seq (.block (pointTableWrite 7808)) verifyEquationPoints)))

def verifyDecodeA : Prog isa :=
  .seq (.block (inputSliceWords 0 0 96 8)) (.seq pointDecode
    (decodedThen (.seq (.block (pointTableWrite 7680)) verifyDecodeR)))

def verifyFinish : List Instr := [.mov .edx (.reg .eax)] ++ restore ++ [.mov .eax (.reg .edx)]

def verifyEquation : Prog isa :=
  .seq (.block (abiSave 3)) (.seq
    (.seq (.block verifyScalar) (.ite .e verifyDecodeA recoverInvalid)) (.block verifyFinish))

end VG.Impl.Ed25519.X86

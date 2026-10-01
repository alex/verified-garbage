import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyWindow

/-! Strict verification with the full 512-bit challenge supplied by the caller. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (at_ sc)

/-- Tail storage survives scalar multiplication's checkpoint and local tables. -/
def pointTableWrite (o : Nat) : List Instr :=
  [.movImm64 .rbx 0] ++ tableAddr o ++ pointToTable

def loadScalarWords : List Instr :=
  [.mov .r8 (.mem (at_ .rdx 0)), .mov .r9 (.mem (at_ .rdx 8)),
    .mov .r10 (.mem (at_ .rdx 16)), .mov .r11 (.mem (at_ .rdx 24))]

def verifyScalar : List Instr :=
  [.mov .rdx (.mem (sc 7944)), .alu .add .rdx (.imm 32)] ++ loadScalarWords ++ scalarSubtract

/-- Compare [X:Y:Z] in slots 0-3 and 4-7 without inversion. -/
def pointEqualOps : List FieldOp := [.mul 8 0 6, .mul 9 4 2, .mul 10 1 6, .mul 11 5 2]

def pointEqual : Prog isa :=
  .seq (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (.ite .e
    (.seq (.block (fieldEqual 10 11)) (.ite .e (.block [.mov32 .rax (.imm 1)]) recoverInvalid))
    recoverInvalid)

/-- Returns 1 in `rax` if `[S]B = R + [k]A`, for `A` at byte 7424 and `R` at byte 7552. -/
def verifyEquationPoints : Prog isa :=
  .seq (.block windowSetup) (.seq aTable (.seq (.block bTable) (.seq (.block windowInit)
    (.seq (.loop byteStepA .ne) (.seq (.loop byteStepAB .ne) (.seq (.block negR) pointEqual))))))

/-- Continue only when a point decoder returned success. -/
def decodedThen (next : Prog isa) : Prog isa :=
  .seq (.block [.alu .test .rax (.reg .rax)]) (.ite .ne next recoverInvalid)

def verifyDecodeR : Prog isa :=
  .seq (.block [.mov .rdx (.mem (sc 7944))]) (.seq pointDecode
    (decodedThen (.seq (.block (pointTableWrite 7552)) verifyEquationPoints)))

def verifyDecodeA : Prog isa :=
  .seq (.block [.mov .rdx (.mem (sc 7936))]) (.seq pointDecode
    (decodedThen (.seq (.block (pointTableWrite 7424)) verifyDecodeR)))

def verifyHeaders : List Instr :=
  [.store (at_ .rdx 7936) .rdi, .store (at_ .rdx 7944) .rsi,
    .store (at_ .rdx 7952) .rax, .mov .rdi (.reg .rdx)]

def verifySetup : List Instr :=
  ([.mov .rax (.reg .rdx), .mov .rdx (.reg .rcx)] : List Instr) ++ scalarSave ++ verifyHeaders

def verifyEquation : Prog isa :=
  .seq (.block verifySetup) (.seq
    (.seq (.block verifyScalar) (.ite .b verifyDecodeA recoverInvalid))
    (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ scalarRestore)))

end VG.Impl.Ed25519.X86_64
